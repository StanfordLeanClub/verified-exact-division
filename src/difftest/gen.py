"""Differential test: Lean `accept` (verified) vs C `efd64_bad_significand` / `efd32_bad_significand`.
Writes the divisor significands, a Lean file that evaluates `accept` on them, and a C file that runs the C check."""
import random, sys, os
here = os.path.dirname(os.path.abspath(__file__))
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 20261110)
N64, N32 = int(sys.argv[2]) if len(sys.argv) > 2 else 3000, int(sys.argv[3]) if len(sys.argv) > 3 else 3000
y64 = [random.getrandbits(52) | (1 << 52) | 1 for _ in range(N64)]
y32 = [random.getrandbits(23) | (1 << 23) | 1 for _ in range(N32)]
# include known edge significands
y64[:4] = [0x1ee635506bf2ef, (1 << 52) | 1, (1 << 53) - 1, 0x15555555555555]
y32[:3] = [(1 << 23) | 1, (1 << 24) - 1, 0x9f0237]
open(os.path.join(here, 'ys64.txt'), 'w').write('\n'.join(map(str, y64)) + '\n')
open(os.path.join(here, 'ys32.txt'), 'w').write('\n'.join(map(str, y32)) + '\n')
print(len(y64), len(y32))
