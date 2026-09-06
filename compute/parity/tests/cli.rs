use std::process::Command;

#[test]
fn invalid_arguments_fail_cleanly() {
    for args in [
        vec![],
        vec!["-1"],
        vec!["1e-1"],
        vec!["4294967294"],
        vec!["18446744073709551615"],
        vec!["10", "-1"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_parity"))
            .args(&args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "args: {args:?}");
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(!error.is_empty() && !error.contains("panicked"), "{error}");
    }
}

#[test]
fn printed_zero_denominators_are_explicit() {
    let output = Command::new(env!("CARGO_BIN_EXE_parity"))
        .args(["5", "2", "7"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout
        .lines()
        .any(|line| line == "2\t2\t2\t0\tinf\t2\t0\t0\t0\t0\t0"));
    assert!(stdout
        .lines()
        .any(|line| line == "7\t0\t0\t0\tundefined\t0\t0\t0\t0\t0\t0"));
}
