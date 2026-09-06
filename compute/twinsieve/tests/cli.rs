use std::process::Command;

#[test]
fn invalid_arguments_fail_cleanly() {
    for args in [
        vec![],
        vec!["-1"],
        vec!["1e-1"],
        vec!["18446744073709551615"],
        vec!["2^64"],
        vec!["5", "6"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_twinsieve"))
            .args(&args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "args: {args:?}");
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(!error.is_empty() && !error.contains("panicked"), "{error}");
    }
}

#[test]
fn reported_odd_checkpoint_is_invariant_under_final_limit() {
    for args in [vec!["5", "3", "5"], vec!["6", "3", "5", "6"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_twinsieve"))
            .args(args)
            .output()
            .unwrap();
        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).unwrap();
        let row = stdout.lines().find(|line| line.starts_with("5\t")).unwrap();
        let columns: Vec<_> = row.split('\t').collect();
        assert_eq!(columns[1], "2");
        let sum: f64 = columns[2].parse().unwrap();
        assert!((sum - (1.0 / 3.0 + 2.0 / 5.0 + 1.0 / 7.0)).abs() < 1e-14);
    }
}
