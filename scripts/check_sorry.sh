#!/usr/bin/env bash
# Compatibility entry point; the portable implementation is standard-library Python.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
if command -v python3 >/dev/null 2>&1; then
  exec python3 "$script_dir/check_proof_hygiene.py" "$@"
fi
exec python "$script_dir/check_proof_hygiene.py" "$@"
