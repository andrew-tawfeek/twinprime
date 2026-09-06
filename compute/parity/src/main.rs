//! parity: the numerical face of the parity obstruction for twin primes.
//!
//! For 2 <= n <= N we compute Omega(n) (number of prime factors with multiplicity) and lpf(n) (least
//! prime factor) by a sieve, and then, for several sifting levels z, restrict to the "sifted"
//! integers n such that n(n+2) has no prime factor <= z, i.e. lpf(n) > z and lpf(n+2) > z.
//! Among those we tabulate Omega(n(n+2)) = Omega(n) + Omega(n+2): its parity and its distribution.
//!
//! These are finite statistics of the product Liouville function lambda(n)lambda(n+2),
//! distinct from the single-function discrepancy in liouville_disc. Equal asymptotic counts
//! do not follow from the formal parity comparison or from a single-function prime number
//! theorem. Twin primes are the class Omega = 2 within the stated support n >= 2.
//! A positive even count divided by zero is displayed as "inf"; 0/0 is "undefined".
//!
//! Usage: parity <N> [z1 z2 ...]     (N up to ~2e9 with 5 bytes per integer of memory)

use std::env;
use std::time::Instant;

fn parse_num(s: &str) -> Result<u64, String> {
    let invalid = || format!("invalid nonnegative integer: {s}");
    if let Some(i) = s.find(['e', 'E']) {
        let exponent: i32 = s[i + 1..].parse().map_err(|_| invalid())?;
        let mantissa = &s[..i];
        let mut digits = String::new();
        let mut decimal_places = None;
        for ch in mantissa.chars() {
            if ch == '.' && decimal_places.is_none() {
                decimal_places = Some(0i64);
            } else if ch.is_ascii_digit() {
                digits.push(ch);
                if let Some(n) = &mut decimal_places {
                    *n += 1;
                }
            } else {
                return Err(invalid());
            }
        }
        if digits.is_empty() {
            return Err(invalid());
        }
        let mut shift = exponent as i64 - decimal_places.unwrap_or(0);
        while shift < 0 && digits.ends_with('0') {
            digits.pop();
            shift += 1;
        }
        if digits.chars().all(|ch| ch == '0') {
            return Ok(0);
        }
        if !(0..=19).contains(&shift) {
            return Err(invalid());
        }
        let value: u64 = digits.parse().map_err(|_| invalid())?;
        return value
            .checked_mul(10u64.pow(shift as u32))
            .ok_or_else(invalid);
    }
    s.parse().map_err(|_| invalid())
}

fn factor_tables(n_max: usize) -> (Vec<u32>, Vec<u8>) {
    let size = n_max + 3;
    // lpf[n] = least prime factor of n (0 = not yet assigned = prime once the sieve is done)
    let mut lpf: Vec<u32> = vec![0; size];
    let mut omega: Vec<u8> = vec![0; size];
    // sieve: for each prime p, mark multiples; add Omega contributions for p, p^2, p^3, ...
    let mut p: usize = 2;
    while p < size {
        if lpf[p] == 0 {
            // p is prime
            let mut m = p;
            while m < size {
                if lpf[m] == 0 {
                    lpf[m] = p as u32;
                }
                omega[m] += 1;
                m += p;
            }
            let mut power = p.checked_mul(p);
            while let Some(pk) = power.filter(|&pk| pk < size) {
                let mut m = pk;
                while m < size {
                    omega[m] += 1;
                    m += pk;
                }
                power = pk.checked_mul(p);
            }
        }
        p += 1;
    }
    (lpf, omega)
}

#[derive(Debug, PartialEq, Eq)]
struct ParityStats {
    sifted: u64,
    even: u64,
    odd: u64,
    hist: [u64; 8],
}

fn parity_stats(n_max: usize, z: u64, lpf: &[u32], omega: &[u8]) -> ParityStats {
    let mut stats = ParityStats {
        sifted: 0,
        even: 0,
        odd: 0,
        hist: [0; 8],
    };
    // n = 1 is excluded explicitly, including at the valid cutoffs z = 0 and z = 1.
    for n in 2..=n_max {
        if lpf[n] as u64 > z && lpf[n + 2] as u64 > z {
            stats.sifted += 1;
            let om = omega[n] as usize + omega[n + 2] as usize;
            if om % 2 == 0 {
                stats.even += 1;
            } else {
                stats.odd += 1;
            }
            stats.hist[om.min(7)] += 1;
        }
    }
    stats
}

fn parity_ratio(even: u64, odd: u64) -> String {
    if odd == 0 {
        if even == 0 {
            "undefined".into()
        } else {
            "inf".into()
        }
    } else {
        format!("{:.6}", even as f64 / odd as f64)
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        return Err("usage: parity <N> [z1 z2 ...]".into());
    }
    let n = parse_num(&args[1])?;
    // Every represented prime factor must fit in lpf's u32 entries, and all
    // table indices and their final loop increments must fit in usize.
    if n > u32::MAX as u64 - 2 || n > (usize::MAX / 2) as u64 - 3 {
        return Err("N is too large for the factor-table representation".into());
    }
    let n_max = n as usize;
    let zs: Vec<u64> = if args.len() > 2 {
        args[2..]
            .iter()
            .map(|s| parse_num(s))
            .collect::<Result<_, _>>()?
    } else {
        vec![10, 100, 1000, 10_000, 100_000, 1_000_000]
    };
    let t0 = Instant::now();
    let (lpf, omega) = factor_tables(n_max);
    let t_sieve = t0.elapsed().as_secs_f64();
    println!("# N={} sieve time={:.1}s", n_max, t_sieve);
    println!("# z\tsifted\teven\todd\teven/odd\ttwins(Omega=2)\tOmega=3\tOmega=4\tOmega=5\tOmega=6\tOmega>=7");
    for &z in &zs {
        let ParityStats {
            sifted,
            even,
            odd,
            hist,
        } = parity_stats(n_max, z, &lpf, &omega);
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            z,
            sifted,
            even,
            odd,
            parity_ratio(even, odd),
            hist[2],
            hist[3],
            hist[4],
            hist[5],
            hist[6],
            hist[7]
        );
    }
    println!("# total time={:.1}s", t0.elapsed().as_secs_f64());
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Independent trial division: no prime-power sieve or table recurrences.
    fn factor(mut n: usize) -> (u32, u8) {
        let mut least = 0;
        let mut omega = 0;
        let mut d = 2;
        while n > 1 {
            while n % d == 0 {
                if least == 0 {
                    least = d as u32;
                }
                omega += 1;
                n /= d;
            }
            d += 1;
        }
        (least, omega)
    }

    #[test]
    fn sieve_factor_tables_agree_with_trial_division() {
        let (lpf, omega) = factor_tables(1000);
        for n in 2..=1002 {
            assert_eq!((lpf[n], omega[n]), factor(n), "n = {n}");
        }
    }

    #[test]
    fn small_histograms_agree_with_independent_factorization() {
        for n_max in [0, 1, 2, 3, 5, 7, 30, 100, 1000] {
            let (lpf, omega) = factor_tables(n_max);
            for z in [0, 1, 2, 3, 5, 10, 31, 1000, u64::MAX] {
                let mut expected = ParityStats {
                    sifted: 0,
                    even: 0,
                    odd: 0,
                    hist: [0; 8],
                };
                for n in 2..=n_max {
                    let (l1, o1) = factor(n);
                    let (l2, o2) = factor(n + 2);
                    if l1 as u64 > z && l2 as u64 > z {
                        expected.sifted += 1;
                        let om = (o1 + o2) as usize;
                        if om % 2 == 0 {
                            expected.even += 1;
                        } else {
                            expected.odd += 1;
                        }
                        expected.hist[om.min(7)] += 1;
                    }
                }
                let actual = parity_stats(n_max, z, &lpf, &omega);
                assert_eq!(actual, expected, "N={n_max}, z={z}");
                assert_eq!(actual.even + actual.odd, actual.sifted);
                assert_eq!(actual.hist.iter().sum::<u64>(), actual.sifted);
            }
        }
    }

    #[test]
    fn zero_denominators_are_not_reported_as_finite_ratios() {
        assert_eq!(parity_ratio(8134, 0), "inf");
        assert_eq!(parity_ratio(0, 0), "undefined");
        assert_eq!(parity_ratio(0, 3), "0.000000");
        assert_eq!(parity_ratio(3, 2), "1.500000");
    }

    #[test]
    fn input_numbers_are_exact_and_invalid_values_are_rejected() {
        for (input, value) in [
            ("0", 0),
            ("1e6", 1_000_000),
            ("1.5E3", 1500),
            ("10e-1", 1),
            ("0e1000", 0),
            ("9007199254740993e0", 9_007_199_254_740_993),
            ("18446744073709551615", u64::MAX),
        ] {
            assert_eq!(parse_num(input), Ok(value));
        }
        for input in [
            "",
            "-1",
            "-1e3",
            "1e-1",
            "1e1000",
            "NaN",
            "inf",
            "18446744073709551616",
            "18446744073709551615e1",
            "1.2.3e4",
        ] {
            assert!(parse_num(input).is_err(), "{input}");
        }
    }
}
