//! liouville_disc: the Liouville discrepancy that bounds every lower-bound sieve for twin primes.
//!
//! `TwinPrime/Parity.lean` proves, for every lower-bound sieve `mu^-` and `z^2 > x`,
//!
//!     sum_{d | P(z)} mu^-(d) * A_d  <=  sum_{d | P(z)} |mu^-(d)| * |Lambda_d|,
//!
//!     A_d      = #{ n <= x : d | n(n+2) },
//!     Lambda_d = sum_{n <= x, d | n(n+2)} lambda(n)      (lambda = Liouville).
//!
//! This program computes `A_d` and `Lambda_d` for every squarefree `d <= D`, and reports
//!   * the largest relative discrepancy  |Lambda_d| / A_d,
//!   * the total  sum_{d <= D squarefree} |Lambda_d|  (the right-hand side for bounded weights of
//!     level `D`), compared with the twin-prime scale  x / (log x)^2  and with  pi_2(x).
//!
//! Usage: liouville_disc <N> <D> [outfile]

use std::env;
use std::io::Write;
use std::time::Instant;

fn parse_num(s: &str) -> u64 {
    if let Some(i) = s.find('e') {
        let m: f64 = s[..i].parse().unwrap();
        let e: i32 = s[i + 1..].parse().unwrap();
        return (m * 10f64.powi(e)).round() as u64;
    }
    s.parse().unwrap()
}

/// lambda(n) = (-1)^Omega(n) for 0 < n < size, stored as i8 (lambda(0) := 0).
fn liouville_table(size: usize) -> Vec<i8> {
    // Omega mod 2 via a sieve over prime powers; primality via a composite bitmap.
    let mut omega: Vec<u8> = vec![0; size];
    let mut composite: Vec<u64> = vec![0; size / 64 + 1];
    let mut p: usize = 2;
    while p < size {
        if composite[p / 64] & (1u64 << (p % 64)) == 0 {
            let mut m = 2 * p;
            while m < size {
                composite[m / 64] |= 1u64 << (m % 64);
                m += p;
            }
            let mut pk = p;
            loop {
                let mut m = pk;
                while m < size {
                    omega[m] ^= 1;
                    m += pk;
                }
                match pk.checked_mul(p) {
                    Some(v) if v < size => pk = v,
                    _ => break,
                }
            }
        }
        p += 1;
    }
    let mut lam: Vec<i8> = vec![0; size];
    for n in 1..size {
        lam[n] = if omega[n] & 1 == 0 { 1 } else { -1 };
    }
    lam
}

fn is_squarefree(mut d: u64) -> (bool, u32) {
    let mut omega = 0u32;
    let mut p = 2u64;
    while p * p <= d {
        if d % p == 0 {
            d /= p;
            omega += 1;
            if d % p == 0 {
                return (false, 0);
            }
        }
        p += 1;
    }
    if d > 1 {
        omega += 1;
    }
    (true, omega)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n_max = parse_num(&args[1]) as usize;
    let d_max = parse_num(&args[2]) as usize;
    let outfile = args.get(3).cloned();
    let t0 = Instant::now();
    let lam = liouville_table(n_max + 1);
    let t_sieve = t0.elapsed().as_secs_f64();
    eprintln!("# N={} D={} liouville table {:.1}s", n_max, d_max, t_sieve);

    // pi_2(N) for the comparison (n, n+2 both prime, n <= N): primes from the same table is not
    // available, so recompute with a quick bit sieve.
    let size = n_max + 3;
    let mut comp: Vec<u64> = vec![0; size / 64 + 1];
    let mut p = 2usize;
    while p * p < size {
        if comp[p / 64] & (1u64 << (p % 64)) == 0 {
            let mut m = p * p;
            while m < size {
                comp[m / 64] |= 1u64 << (m % 64);
                m += p;
            }
        }
        p += 1;
    }
    let is_prime = |n: usize| n >= 2 && comp[n / 64] & (1u64 << (n % 64)) == 0;
    let mut pi2: u64 = 0;
    for n in 2..=n_max {
        if is_prime(n) && is_prime(n + 2) {
            pi2 += 1;
        }
    }

    // squarefree d <= D with their roots r mod d of r(r+2) = 0
    let ds: Vec<(u64, u32)> = (1..=d_max as u64)
        .filter_map(|d| {
            let (sf, om) = is_squarefree(d);
            if sf {
                Some((d, om))
            } else {
                None
            }
        })
        .collect();
    let nthreads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);
    // results[i] = (A_d, Lambda_d) for ds[i]
    let mut results: Vec<(u64, i64)> = vec![(0, 0); ds.len()];
    {
        let lam = &lam;
        let ds = &ds;
        let next = std::sync::atomic::AtomicUsize::new(0);
        let out: Vec<std::sync::Mutex<Vec<(usize, u64, i64)>>> = (0..nthreads)
            .map(|_| std::sync::Mutex::new(Vec::new()))
            .collect();
        std::thread::scope(|s| {
            for t in 0..nthreads {
                let next = &next;
                let out = &out[t];
                s.spawn(move || loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= ds.len() {
                        break;
                    }
                    let (d, _) = ds[i];
                    let du = d as usize;
                    let mut a: u64 = 0;
                    let mut l: i64 = 0;
                    for r in 0..du {
                        if (r * (r + 2)) % du == 0 {
                            let mut n = r;
                            while n <= n_max {
                                a += 1;
                                l += lam[n] as i64;
                                n += du;
                            }
                        }
                    }
                    out.lock().unwrap().push((i, a, l));
                });
            }
        });
        for m in out {
            for (i, a, l) in m.into_inner().unwrap() {
                results[i] = (a, l);
            }
        }
    }
    let t_all = t0.elapsed().as_secs_f64();

    let x = n_max as f64;
    let scale = x / (x.ln() * x.ln());
    let mut total_abs: f64 = 0.0;
    let mut max_rel: f64 = 0.0;
    let mut max_rel_d: u64 = 0;
    let mut max_abs: i64 = 0;
    let mut max_abs_d: u64 = 0;
    for (i, &(d, _)) in ds.iter().enumerate() {
        let (a, l) = results[i];
        total_abs += (l.abs()) as f64;
        if a > 0 {
            let rel = l.abs() as f64 / a as f64;
            if rel > max_rel {
                max_rel = rel;
                max_rel_d = d;
            }
        }
        if l.abs() > max_abs {
            max_abs = l.abs();
            max_abs_d = d;
        }
    }
    let mut w: Box<dyn Write> = match outfile {
        Some(f) => Box::new(std::fs::File::create(f).unwrap()),
        None => Box::new(std::io::stdout()),
    };
    writeln!(
        w,
        "# N={} D={} squarefree_d={} time={:.1}s (table {:.1}s)",
        n_max,
        d_max,
        ds.len(),
        t_all,
        t_sieve
    )
    .unwrap();
    writeln!(w, "# pi_2(N)={}  x/log^2x={:.1}", pi2, scale).unwrap();
    writeln!(w, "# sum_{{d<=D sqfree}} |Lambda_d| = {:.0}  ratio to x/log^2x = {:.4}  ratio to pi_2 = {:.4}",
        total_abs, total_abs / scale, total_abs / pi2 as f64).unwrap();
    writeln!(
        w,
        "# max |Lambda_d|/A_d = {:.3e} at d={}   max |Lambda_d| = {} at d={}",
        max_rel, max_rel_d, max_abs, max_abs_d
    )
    .unwrap();
    writeln!(
        w,
        "# d\tomega\tA_d\tLambda_d\tLambda_d/A_d\tLambda_d*sqrt(d/x)"
    )
    .unwrap();
    for (i, &(d, om)) in ds.iter().enumerate() {
        let (a, l) = results[i];
        writeln!(
            w,
            "{}\t{}\t{}\t{}\t{:.3e}\t{:.4}",
            d,
            om,
            a,
            l,
            if a > 0 { l as f64 / a as f64 } else { 0.0 },
            l as f64 * (d as f64 / x).sqrt()
        )
        .unwrap();
    }
    eprintln!(
        "# done {:.1}s; sum|Lambda_d|={:.0} vs x/log^2x={:.0}, pi_2={}",
        t_all, total_abs, scale, pi2
    );
}
