"""
Numerical Galerkin estimates for the Maynard–Tao functional M_k (GPU or CPU).

For F : R_k -> R supported on the simplex R_k = {t_i >= 0, sum t_i <= 1},
    I(F)   = int F^2,
    J_m(F) = int_{R_{k-1}} ( int F dt_m )^2   (integrate out the m-th variable),
    M_k    = sup_F  sum_m J_m(F) / I(F).

Maynard's theorem: if the primes have level of distribution theta and M_k > 2m/theta, then
infinitely many n have at least m+1 primes among n+h_1, ..., n+h_k for any admissible k-tuple.
Two primes (m = 1) in an admissible PAIR (k = 2, e.g. {0, 2} = twin primes) would need
M_2 > 2/theta >= 2.  The standard upper bound M_k <= k/(k-1) * log k gives M_2 <= 2 log 2 < 2.
This script approximates M_k^{(N)} by a Galerkin discretisation with piecewise
constant functions on cubes of side h = 1/N that lie inside R_k (multi-index i with sum(i) <= N-k),
and a floating-point power iteration. Exact Rayleigh quotients in this subspace
are lower bounds for M_k, but the printed values have no certified rounding
interval. No monotonicity across arbitrary grids or O(1/N) error is established here.

For piecewise constant F with cell values c[i_1,...,i_k] (cells with sum(i) <= N-k lie in R_k):
    I(F)   = h^k * sum c^2
    J_m(F) = h^{k+1} * sum_{i_{≠m}} ( sum_{i_m} c )^2
so sum_m J_m / I = h * <c, A c> / <c, c> with (A c) = sum_m broadcast_m(sum over axis m of c),
restricted to the admissible cells.  The largest eigenvalue of h*A (masked) is M_k^{(N)}.

Usage: python maynard_mk.py
"""
import math, time, sys
import torch

def mk_lower_bound(k: int, N: int, iters: int = 3000, dev=None, dtype=torch.float64):
    """Return an uncertified floating-point Rayleigh estimate and iteration count."""
    if k < 2 or N < k or iters < 1:
        raise ValueError("require k >= 2, N >= k, and iters >= 1")
    dev = dev or torch.device("cuda" if torch.cuda.is_available() else "cpu")
    h = 1.0 / N
    # admissible cells: multi-index i with sum(i) <= N-k (the cube then lies inside the simplex)
    idx = torch.arange(N, device=dev)
    grids = torch.meshgrid(*([idx] * k), indexing="ij")
    s = sum(grids)
    mask = (s <= N - k).to(dtype)
    # symmetric start vector: F = 1 on admissible cells (a reasonable initial guess)
    c = mask.clone()
    c /= c.norm()
    lam = 0.0
    for it in range(iters):
        Ac = torch.zeros_like(c)
        for m in range(k):
            Ac += c.sum(dim=m, keepdim=True).expand_as(c)
        Ac *= mask
        Ac *= h
        lam_new = torch.dot(c.flatten(), Ac.flatten()).item()
        nrm = Ac.norm()
        c = Ac / nrm
        if it > 50 and abs(lam_new - lam) < 1e-13 * max(1.0, abs(lam_new)):
            lam = lam_new
            break
        lam = lam_new
    return lam, it + 1

def main():
    dev = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"# device={dev} {torch.cuda.get_device_name(0) if dev.type=='cuda' else ''}")
    print("# k\tN\tM_k Galerkin estimate (uncertified)\titers\tsecs\tupper bound k/(k-1) log k")
    plan = {2: [200, 400, 800, 1600, 3200], 3: [50, 100, 200, 300], 4: [24, 40, 60, 80], 5: [12, 20, 30, 36]}
    results = {}
    for k, Ns in plan.items():
        ub = k / (k - 1) * math.log(k)
        for N in Ns:
            t0 = time.time()
            lam, it = mk_lower_bound(k, N, dev=dev)
            el = time.time() - t0
            results.setdefault(k, []).append((N, lam))
            print(f"{k}\t{N}\t{lam:.6f}\t{it}\t{el:.1f}\t{ub:.6f}")
            sys.stdout.flush()
    # Richardson extrapolation (error ~ a/N): M ≈ (N2*l2 - N1*l1)/(N2 - N1) from the two finest levels
    print("# Richardson extrapolation from the two finest levels (heuristic, not a bound):")
    for k, rs in results.items():
        (N1, l1), (N2, l2) = rs[-2], rs[-1]
        ext = (N2 * l2 - N1 * l1) / (N2 - N1)
        print(f"{k}\tM_{k} ~ {ext:.5f}   (threshold for two primes under EH: 2;  unconditional theta=1/2: 4)")

if __name__ == "__main__":
    main()
