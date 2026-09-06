#!/usr/bin/env python3
"""Conservative Lean source and selected-declaration axiom checks.

This is a lexical guard, not a Lean parser, macro expander, or replacement for
compilation and kernel checking. An axiom log must come from a successful run of
`lake env lean scripts/Axioms.lean`; this script cannot authenticate its freshness.
Only Python's standard library is required. Source paths are independent of cwd.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


FORBIDDEN_TOKENS = {
    "sorry", "admit", "axiom", "native_decide", "unsafe", "implemented_by", "extern",
    "sorryAx", "trustCompiler", "ofReduceBool", "ofReduceNat",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TOKEN = re.compile(r"«[^»]*»|(?:[^\W\d]|_)[\w'!?]*|[^\s]", re.UNICODE)
RAW_STRING = re.compile(r'r(#+)?"')
CHAR_LITERAL = re.compile(r"'(?:[^'\\\n]|\\(?:u\{[0-9a-fA-F]+\}|u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[^\n]))'")
AXIOM_HEADER = re.compile(
    r"^'(?P<name>[^\n]+)'[ \t]+(?P<kind>depends on axioms:|does not depend on any axioms)",
    re.MULTILINE,
)
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


class HygieneError(ValueError):
    """An unreadable, incomplete, or disallowed input."""


def location(text: str, offset: int) -> str:
    return f"{text.count(chr(10), 0, offset) + 1}:{offset - text.rfind(chr(10), 0, offset)}"


def mask_lean(text: str, label: str = "<input>") -> str:
    """Blank nested comments and literals, preserving offsets and newlines.

    Quoted identifiers are retained. Raw strings use matching hash delimiters.
    String interpolation is not parsed as Lean code; like other string contents
    it is ignored by this lexical check. Compilation and axiom auditing remain
    necessary, including for code produced by macros or syntax quotations.
    """
    result = list(text)

    def blank(start: int, end: int) -> None:
        for pos in range(start, end):
            if text[pos] not in "\r\n":
                result[pos] = " "

    def fail(start: int, what: str) -> None:
        raise HygieneError(f"{label}:{location(text, start)}: unterminated {what}")

    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            blank(start, i)
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                fail(start, "block comment")
            blank(start, i)
        elif text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                fail(start, "quoted identifier")
            i = end + 1
        elif (raw := RAW_STRING.match(text, i)) and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")
        ):
            delimiter = '"' + (raw.group(1) or "")
            end = text.find(delimiter, raw.end())
            if end < 0:
                fail(start, "raw string")
            i = end + len(delimiter)
            blank(start, i)
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                fail(start, "string")
            if i > len(text):
                fail(start, "string")
            blank(start, i)
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")):
            char = CHAR_LITERAL.match(text, i)
            if char:
                i = char.end()
                blank(start, i)
            else:
                i += 1  # Apostrophes also occur in Lean syntax quotations.
        else:
            i += 1
    return "".join(result)


def token_value(raw: str) -> str:
    return raw[1:-1] if raw.startswith("«") and raw.endswith("»") else raw


def source_findings(text: str, label: str) -> list[str]:
    tokens = list(TOKEN.finditer(mask_lean(text, label)))
    findings = []
    for index, token in enumerate(tokens):
        value = token_value(token.group())
        if value in FORBIDDEN_TOKENS:
            findings.append(f"{label}:{location(text, token.start())}: forbidden token {value}")
        if value == "debug.skipKernelTC" or (
            value == "debug" and index + 2 < len(tokens)
            and tokens[index + 1].group() == "."
            and token_value(tokens[index + 2].group()) == "skipKernelTC"
        ):
            findings.append(f"{label}:{location(text, token.start())}: forbidden option debug.skipKernelTC")
    return findings


def read_text(path: Path) -> str:
    data = path.read_bytes()
    # PowerShell may write UTF-8 or BOM-marked UTF-16 logs.
    encoding = "utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig"
    return data.decode(encoding).replace("\r\n", "\n")


def scan_sources(root: Path) -> tuple[int, list[str]]:
    if not (root / "TwinPrime.lean").is_file() or not (root / "TwinPrime").is_dir():
        raise HygieneError(f"{root}: expected TwinPrime.lean and TwinPrime/ sources")
    files = [root / "TwinPrime.lean", *sorted((root / "TwinPrime").rglob("*.lean"))]
    findings = []
    for path in files:
        label = path.relative_to(root).as_posix()
        try:
            findings.extend(source_findings(read_text(path), label))
        except HygieneError as error:
            findings.append(str(error))
    return len(files), findings


def is_identifier(token: str) -> bool:
    return token.startswith("«") or bool(re.fullmatch(r"(?:[^\W\d]|_)[\w'!?]*", token))


def canonical_name(name: str) -> str:
    return name.removeprefix("_root_.")


def audit_selections(path: Path) -> set[str]:
    """Read explicit #print axioms names; duplicate selections form one name."""
    text = read_text(path)
    tokens = list(TOKEN.finditer(mask_lean(text, str(path))))
    selections = set()
    for index in range(len(tokens) - 2):
        if [token.group() for token in tokens[index:index + 3]] != ["#", "print", "axioms"]:
            continue
        cursor = index + 3
        if cursor >= len(tokens) or not is_identifier(tokens[cursor].group()):
            raise HygieneError(f"{path}:{location(text, tokens[index].start())}: missing #print axioms name")
        parts = [tokens[cursor].group()]
        cursor += 1
        while cursor < len(tokens) and tokens[cursor].group() == ".":
            cursor += 1
            if cursor >= len(tokens) or not is_identifier(tokens[cursor].group()):
                raise HygieneError(f"{path}: malformed qualified #print axioms name")
            parts.append(tokens[cursor].group())
            cursor += 1
        selections.add(canonical_name(".".join(parts)))
    if not selections:
        raise HygieneError(f"{path}: no #print axioms selections found")
    return selections


def check_axiom_log(path: Path, expected: set[str]) -> int:
    text = ANSI_ESCAPE.sub("", read_text(path))
    if not text.strip():
        raise HygieneError(f"{path}: empty axiom log")
    if not text.endswith("\n"):
        raise HygieneError(f"{path}: log has no final newline; it may be truncated")
    if re.search(r"\berror:|declaration uses ['\"]sorry['\"]", text, re.IGNORECASE):
        raise HygieneError(f"{path}: Lean reported an error or a proof hole")
    entries = []
    consumed = list(text)
    for match in AXIOM_HEADER.finditer(text):
        name = canonical_name(match.group("name"))
        cursor = match.end()
        axioms = []
        if match.group("kind") == "depends on axioms:":
            while cursor < len(text) and text[cursor].isspace():
                cursor += 1
            if cursor >= len(text) or text[cursor] != "[":
                raise HygieneError(f"{path}: missing axiom list for {name}")
            end = text.find("]", cursor + 1)
            if end < 0:
                raise HygieneError(f"{path}: truncated axiom list for {name}")
            body = text[cursor + 1:end].strip()
            axioms = [part.strip() for part in body.split(",")] if body else []
            cursor = end + 1
        endline = text.find("\n", cursor)
        if endline < 0 or text[cursor:endline].strip() not in ("", "."):
            raise HygieneError(f"{path}: malformed axiom entry for {name}")
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise HygieneError(f"{path}: {name} depends on disallowed axioms: {', '.join(sorted(unexpected))}")
        entries.append(name)
        for pos in range(match.start(), endline):
            consumed[pos] = " " if text[pos] != "\n" else "\n"
    leftovers = "".join(consumed)
    if re.search(r"axioms:|does not depend on any axioms|^'.*'\s+(?:depends|does not depend)", leftovers, re.MULTILINE):
        raise HygieneError(f"{path}: malformed or truncated axiom output")
    if not entries:
        raise HygieneError(f"{path}: no axiom audit entries found")
    duplicates = sorted(name for name, count in Counter(entries).items() if count > 1)
    if duplicates:
        raise HygieneError(f"{path}: duplicate audit entries: {', '.join(duplicates)}")
    missing, extra = expected - set(entries), set(entries) - expected
    if missing or extra:
        detail = []
        if missing:
            detail.append(f"missing {len(missing)}: {', '.join(sorted(missing)[:8])}")
        if extra:
            detail.append(f"unexpected {len(extra)}: {', '.join(sorted(extra)[:8])}")
        raise HygieneError(f"{path}: audit selections do not match ({'; '.join(detail)})")
    return len(entries)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--axiom-log", type=Path, help="complete output of lake env lean scripts/Axioms.lean")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parent.parent
    try:
        count, findings = scan_sources(root)
        if findings:
            raise HygieneError("\n".join(findings))
        print(f"OK: {count} Lean sources contain no forbidden proof or trust-bypass tokens.")
        if args.axiom_log is not None:
            expected = audit_selections(root / "scripts" / "Axioms.lean")
            entries = check_axiom_log(args.axiom_log, expected)
            print(f"OK: {entries} axiom entries exactly match the selections; only propext, Classical.choice, Quot.sound allowed.")
    except (HygieneError, OSError, UnicodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
