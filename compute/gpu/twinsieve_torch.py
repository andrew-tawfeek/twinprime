"""
GPU segmented sieve for twin primes (PyTorch / CUDA).

Independent re-implementation of compute/twinsieve (Rust, CPU) on the GPU, used to cross-check
the exact counts pi_2(x).  Representation: one uint8 per odd number in a segment.  Multiples of
each odd prime p <= sqrt(limit) are cleared with a strided slice assignment (one CUDA kernel per
prime per segment).  Twin pairs (n, n+2) correspond to adjacent flags.

Usage:  python twinsieve_torch.py 1e11 [checkpoints ...]
"""
import sys, time, math
import numpy as np
import torch

def parse(s: str) -> int:
    return int(float(s))

def small_primes(n: int) -> np.ndarray:
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    p = np.nonzero(s)[0]
    return p[p >= 3]

def main():
    limit = parse(sys.argv[1])
    cps = sorted(set(parse(a) for a in sys.argv[2:])) or [limit]
    assert cps[-1] <= limit
    dev = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"# device={dev} {torch.cuda.get_device_name(0) if dev.type=='cuda' else ''}")
    primes = small_primes(int(math.isqrt(limit)) + 2)
    primes_t = torch.from_numpy(primes.astype(np.int64)).to(dev)
    seg_odd = 1 << 27                      # odd numbers per segment (128 MiB of flags)
    seg_span = 2 * seg_odd
    counts = np.zeros(len(cps), dtype=np.int64)
    t0 = time.time()
    lo = 1
    flags = torch.empty(seg_odd + 1, dtype=torch.uint8, device=dev)
    while lo <= limit:
        hi = min(lo + seg_span, limit + 2)   # sieve odd n in [lo, hi) plus one extra for the pair
        n_odd = (hi - lo + 1) // 2 + 1
        f = flags[:n_odd]
        f.fill_(1)
        top = lo + 2 * n_odd
        # first odd multiple >= max(p*p, lo) of each prime, as an index into f
        pp = primes_t * primes_t
        start = torch.where(pp >= lo, pp, ((lo + primes_t - 1) // primes_t) * primes_t)
        start = torch.where(start % 2 == 0, start + primes_t, start)
        idx0 = ((start - lo) // 2).cpu().numpy()
        ps = primes
        for p, i0 in zip(ps, idx0):
            if p * p >= top:
                break
            if i0 < n_odd:
                f[i0::p] = 0
        if lo == 1:
            f[0] = 0
        # twin pairs with lower member n = lo + 2i, need n <= limit and n < hi
        pair = (f[:-1] & f[1:]).to(torch.int32)
        # prefix positions for checkpoints inside this segment
        cs = torch.cumsum(pair, 0)
        for k, c in enumerate(cps):
            if c < lo:
                continue
            if c >= hi - 2 + 2:   # whole segment below checkpoint: count lower members n < hi
                nmax = min(hi - 1, limit)
            else:
                nmax = c
            imax = (nmax - lo) // 2          # largest index with n <= nmax
            if imax >= 0:
                counts[k] += int(cs[min(imax, cs.numel() - 1)].item())
        lo = hi if hi % 2 == 1 else hi + 1
    if dev.type == "cuda":
        torch.cuda.synchronize()
    el = time.time() - t0
    print(f"# limit={limit} elapsed={el:.1f}s")
    print("# x\tpi2(x)")
    for c, n in zip(cps, counts):
        print(f"{c}\t{n}")

if __name__ == "__main__":
    main()
