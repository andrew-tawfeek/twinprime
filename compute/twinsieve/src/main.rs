//! twinsieve: exact counts of twin prime pairs (p, p+2) with p <= x, for x up to ~1e13,
//! together with the Brun partial sums  S(x) = sum_{p<=x, p+2 prime} (1/p + 1/(p+2)).
//!
//! Method: segmented sieve of Eratosthenes over odd numbers only, bit-packed (1 bit per odd
//! number), segments processed in parallel by std::thread::scope with an atomic work counter.
//! Each segment [lo, hi) is sieved on [lo, hi+2) so the pair (hi-2, hi) straddling the boundary
//! is attributed to exactly one segment (the one containing the lower member).
//!
//! Usage:  twinsieve <limit> [checkpoints...]
//!   e.g.  twinsieve 1e12 1e6 1e7 1e8 1e9 1e10 1e11 1e12
//! Output: one line per checkpoint c:  c  pi_2(c)  S(c)  HL(c)  ratio  Brun-extrapolation

use std::env;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

fn parse_num(s: &str) -> Result<u64, String> {
    let invalid = || format!("invalid nonnegative integer: {s}");
    if let Some(i) = s.find('^') {
        let b: u64 = s[..i].parse().map_err(|_| invalid())?;
        let e: u32 = s[i + 1..].parse().map_err(|_| invalid())?;
        return b.checked_pow(e).ok_or_else(invalid);
    }
    // Parse scientific notation exactly; floating-point rounding can change an endpoint.
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

/// Simple sieve for primes up to n (inclusive); returns the odd primes >= 3.
fn small_primes(n: u64) -> Vec<u32> {
    let n = n as usize;
    let mut is = vec![true; n + 1];
    let mut ps = Vec::new();
    if n >= 2 {
        is[0] = false;
        is[1] = false;
    }
    let mut i = 2usize;
    while i * i <= n {
        if is[i] {
            let mut j = i * i;
            while j <= n {
                is[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    for i in 3..=n {
        if is[i] {
            ps.push(i as u32);
        }
    }
    ps
}

/// Per-segment result: for each checkpoint index k, the number of twin pairs with lower member
/// p in [lo, hi) and p <= checkpoint[k], and the corresponding Brun partial sums.
struct SegResult {
    counts: Vec<u64>,
    sums: Vec<f64>,
}

fn sieve_segment(
    lo: u64,
    hi: u64,
    primes: &[u32],
    checkpoints: &[u64],
    bits: &mut Vec<u64>,
) -> SegResult {
    // odd numbers in [lo, hi + 2): index i <-> n = lo + 2i, lo odd.
    debug_assert!(lo % 2 == 1);
    debug_assert!(hi % 2 == 1 && hi > lo);
    let len = ((hi + 2 - lo) / 2) as usize;
    let words = (len + 63) / 64;
    bits.clear();
    bits.resize(words, !0u64);
    let top = hi + 2;
    for &p in primes {
        let p = p as u64;
        if p * p >= top {
            break;
        }
        let mut start = p * p;
        if start < lo {
            let q = (lo + p - 1) / p;
            start = q * p;
            if start % 2 == 0 {
                start += p;
            }
        }
        if start >= top {
            continue;
        }
        let mut i = ((start - lo) / 2) as usize;
        let step = p as usize;
        while i < len {
            bits[i >> 6] &= !(1u64 << (i & 63));
            i += step;
        }
    }
    if lo == 1 {
        bits[0] &= !1u64; // 1 is not prime
    }
    let npairs_idx = ((hi - lo) / 2) as usize;
    let mut counts = vec![0u64; checkpoints.len()];
    let mut sums = vec![0f64; checkpoints.len()];
    let mut s = 0f64;
    let mut c = 0f64;
    let mut cnt = 0u64;
    let mut k = 0usize;
    while k < checkpoints.len() && checkpoints[k] < lo {
        k += 1;
    }
    for i in 0..npairs_idx {
        let n = lo + 2 * i as u64;
        while k < checkpoints.len() && checkpoints[k] < n {
            counts[k] = cnt;
            sums[k] = s;
            k += 1;
        }
        let a = (bits[i >> 6] >> (i & 63)) & 1;
        let j = i + 1;
        let b = (bits[j >> 6] >> (j & 63)) & 1;
        if (a & b) == 1 {
            cnt += 1;
            let term = 1.0 / n as f64 + 1.0 / (n + 2) as f64;
            let y = term - c;
            let t = s + y;
            c = (t - s) - y;
            s = t;
        }
    }
    while k < checkpoints.len() {
        counts[k] = cnt;
        sums[k] = s;
        k += 1;
    }
    SegResult { counts, sums }
}

/// Segments own lower members only. Both endpoints are odd, and each segment
/// allocates one extra odd flag for the upper member of its last possible pair.
fn count_twins(limit: u64, checkpoints: &[u64], seg_odd: u64, nthreads: usize) -> SegResult {
    assert!(seg_odd > 0 && nthreads > 0);
    let sqrt = (limit + 2).isqrt();
    let primes = small_primes(sqrt);
    let odd_count = limit.div_ceil(2);
    let nsegs = odd_count.div_ceil(seg_odd);
    let next = AtomicU64::new(0);
    let results: Vec<SegResult> = std::thread::scope(|sc| {
        let mut handles = Vec::new();
        for _ in 0..nthreads {
            handles.push(sc.spawn(|| {
                let mut bits: Vec<u64> = Vec::new();
                let mut acc_counts = vec![0u64; checkpoints.len()];
                let mut acc_sums = vec![0f64; checkpoints.len()];
                loop {
                    let si = next.fetch_add(1, Ordering::Relaxed);
                    if si >= nsegs {
                        break;
                    }
                    let first = si * seg_odd;
                    let lo = 2 * first + 1;
                    let hi = lo + 2 * (odd_count - first).min(seg_odd);
                    let r = sieve_segment(lo, hi, &primes, &checkpoints, &mut bits);
                    for k in 0..checkpoints.len() {
                        acc_counts[k] += r.counts[k];
                        acc_sums[k] += r.sums[k];
                    }
                }
                SegResult {
                    counts: acc_counts,
                    sums: acc_sums,
                }
            }));
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut counts = vec![0u64; checkpoints.len()];
    let mut sums = vec![0f64; checkpoints.len()];
    for r in &results {
        for k in 0..checkpoints.len() {
            counts[k] += r.counts[k];
            sums[k] += r.sums[k];
        }
    }
    SegResult { counts, sums }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        return Err("usage: twinsieve <limit> [checkpoints...]".into());
    }
    let limit = parse_num(&args[1])?;
    // The final odd exclusive endpoint and the partner flag require up to limit + 4.
    if limit > u64::MAX - 4 {
        return Err("limit is too large for the segment endpoints".into());
    }
    let mut checkpoints: Vec<u64> = if args.len() > 2 {
        args[2..]
            .iter()
            .map(|s| parse_num(s))
            .collect::<Result<_, _>>()?
    } else {
        vec![limit]
    };
    checkpoints.sort_unstable();
    checkpoints.dedup();
    if *checkpoints.last().unwrap() > limit {
        return Err("checkpoints must be <= limit".into());
    }
    let t0 = Instant::now();
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    let seg_odd = 1 << 21;
    let nsegs = limit.div_ceil(2).div_ceil(seg_odd);
    let SegResult { counts, sums } = count_twins(limit, &checkpoints, seg_odd, nthreads);
    let elapsed = t0.elapsed().as_secs_f64();
    // twin prime constant C_2 = prod_{p>2} (1 - 1/(p-1)^2) = 0.66016181584686957392...
    let two_c2 = 2.0 * 0.660_161_815_846_869_573_9_f64;
    println!(
        "# limit={} threads={} segments={} elapsed={:.2}s",
        limit, nthreads, nsegs, elapsed
    );
    println!("# x\tpi2(x)\tS(x)=sum(1/p+1/(p+2))\tHL(x)=2C2*int_2^x dt/ln^2 t\tpi2/HL\tB2_extrap=S(x)+4C2/ln(x)");
    for k in 0..checkpoints.len() {
        let x = checkpoints[k] as f64;
        let hl = two_c2 * li2(x);
        let ratio = if hl > 0.0 {
            format!("{:.6}", counts[k] as f64 / hl)
        } else {
            "undefined".into()
        };
        let extrap = if x > 1.0 {
            format!("{:.12}", sums[k] + 2.0 * two_c2 / x.ln())
        } else {
            "undefined".into()
        };
        println!(
            "{}\t{}\t{:.15}\t{:.3}\t{}\t{}",
            checkpoints[k], counts[k], sums[k], hl, ratio, extrap
        );
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

/// int_2^x dt / ln(t)^2 via composite Simpson after t = e^u.
fn li2(x: f64) -> f64 {
    if x <= 2.0 {
        return 0.0;
    }
    let a = 2f64.ln();
    let b = x.ln();
    let n = 200_000usize;
    let h = (b - a) / n as f64;
    let f = |u: f64| u.exp() / (u * u);
    let mut s = f(a) + f(b);
    for i in 1..n {
        let u = a + i as f64 * h;
        s += if i % 2 == 1 { 4.0 * f(u) } else { 2.0 * f(u) };
    }
    s * h / 3.0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Independent ordinary sieve, including both extra units for the upper member.
    fn reference(limit: usize) -> SegResult {
        let mut prime = vec![true; limit + 3];
        prime[0] = false;
        prime[1] = false;
        for p in 2..prime.len() {
            if prime[p] {
                for m in (2 * p..prime.len()).step_by(p) {
                    prime[m] = false;
                }
            }
        }
        let mut counts = vec![0; limit + 1];
        let mut sums = vec![0.0; limit + 1];
        for n in 1..=limit {
            counts[n] = counts[n - 1];
            sums[n] = sums[n - 1];
            if prime[n] && prime[n + 2] {
                counts[n] += 1;
                sums[n] += 1.0 / n as f64 + 1.0 / (n + 2) as f64;
            }
        }
        SegResult { counts, sums }
    }

    fn compare(actual: &SegResult, expected: &SegResult, checkpoints: &[u64]) {
        for (k, &checkpoint) in checkpoints.iter().enumerate() {
            let c = checkpoint as usize;
            assert_eq!(actual.counts[k], expected.counts[c], "checkpoint {c}");
            assert!(
                (actual.sums[k] - expected.sums[c]).abs() < 1e-12,
                "Brun sum at {c}: {} vs {}",
                actual.sums[k],
                expected.sums[c]
            );
        }
    }

    #[test]
    fn every_small_endpoint_and_checkpoint_agrees_with_reference() {
        let expected = reference(128);
        for limit in 0..=128 {
            let checkpoints: Vec<u64> = (0..=limit).collect();
            for seg_odd in [1, 2, 3, 7, 64] {
                compare(
                    &count_twins(limit, &checkpoints, seg_odd, 1),
                    &expected,
                    &checkpoints,
                );
            }
        }
    }

    #[test]
    fn checkpoint_counts_and_sums_do_not_depend_on_final_limit_or_workers() {
        let expected = reference(1001);
        let checkpoints = [0, 1, 2, 3, 5, 7, 11, 13, 17, 29];
        for limit in [29, 30, 31, 127, 128, 129, 1000, 1001] {
            for nthreads in [1, 3] {
                compare(
                    &count_twins(limit, &checkpoints, 3, nthreads),
                    &expected,
                    &checkpoints,
                );
            }
        }
    }

    #[test]
    fn twin_crossing_segment_boundary_is_owned_by_its_lower_member() {
        let primes = small_primes(10);
        let checkpoints = [3, 5, 6, 7, 11, 13];
        let mut bits = Vec::new();
        // The pair (5, 7) crosses the first segment's exclusive boundary at 7.
        let left = sieve_segment(1, 7, &primes, &checkpoints, &mut bits);
        let right = sieve_segment(7, 13, &primes, &checkpoints, &mut bits);
        assert_eq!(left.counts, [1, 2, 2, 2, 2, 2]);
        assert_eq!(right.counts, [0, 0, 0, 0, 1, 1]);
        let combined = SegResult {
            counts: left
                .counts
                .iter()
                .zip(&right.counts)
                .map(|(a, b)| a + b)
                .collect(),
            sums: left
                .sums
                .iter()
                .zip(&right.sums)
                .map(|(a, b)| a + b)
                .collect(),
        };
        compare(&combined, &reference(13), &checkpoints);
    }

    #[test]
    fn production_segment_boundary_agrees_with_reference() {
        let boundary = 1 << 22;
        let limit = boundary + 33;
        let checkpoints = [
            boundary - 3,
            boundary - 2,
            boundary - 1,
            boundary,
            boundary + 1,
            boundary + 2,
            boundary + 3,
            limit,
        ];
        compare(
            &count_twins(limit, &checkpoints, 1 << 21, 2),
            &reference(limit as usize),
            &checkpoints,
        );
    }

    #[test]
    fn input_numbers_are_exact_and_invalid_values_are_rejected() {
        for (input, value) in [
            ("0", 0),
            ("1e6", 1_000_000),
            ("1.5E3", 1500),
            ("10e-1", 1),
            ("0e1000", 0),
            ("2^10", 1024),
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
            "2^64",
            "1.2.3e4",
        ] {
            assert!(parse_num(input).is_err(), "{input}");
        }
    }
}
