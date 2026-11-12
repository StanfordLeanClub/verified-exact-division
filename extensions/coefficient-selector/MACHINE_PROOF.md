# Checked machine implementation of binary32 /3

`Div3Machine.machine_correct` proves total correctness of one specific x86-64
image of `certified_div3`. It follows the actual 32-element, 8-element, and
scalar loops, including the compiler's signed-minimum vector guard and its
eager scalar multiply/FMA before the fallback decision. This is an additional
artifact contract; it does not certify arbitrary recompilation of the inline
header.

The image contains 505 instruction bytes and 27 bytes of padding/constants,
with SHA-256
`a08a38145390d6ebe4fcc924149887c3fe12e560f50776482570f2149cfe6940`.
There are 107 instructions. The entry uses the System V x86-64 calling
convention, including on Windows through the explicit `sysv_abi` declaration
in `native/certified_div3.h`. It is a leaf: no calls or stack spills.

## What the theorem says

For every permitted length, initial register state, and byte-addressed memory,
there is a finite instruction execution ending in a return. Each destination
word decodes to the correctly rounded reference quotient of the original
source word. This includes subnormals, signed zeros, infinities, and NaN class.
All bytes outside the destination range are unchanged. Each load/store lies
inside the declared source, destination, image, or return-address region.
The saved return address is read unchanged, RSP advances by eight, and every
general register except RAX, RCX, and RSP is preserved. `memory_permissions`
turns these bounds into per-byte read/write permission guarantees.

The caller supplies accessible source and destination ranges of `4*n` bytes,
either disjoint or identical. Partial overlap is excluded. Address arithmetic
must satisfy `Valid`: representable pointers and lengths, nonwrapping buffer
and image extents, an accessible eight-byte return slot with a nonwrapping
post-return RSP, and destination disjoint from the executable image and return
slot. The image must be loaded unchanged. Actual page mappings, executable
permissions, a valid executable return target, the caller's ABI, and absence of concurrent buffer/code mutation
are environmental requirements. `n=0` needs no buffer access.

The floating-point contract remains nearest-even, gradual underflow,
FTZ/DAZ disabled, masked exceptions, and AVX2/FMA enabled. Exception flags,
traps, NaN payload/sign/signaling status, `errno`, and timing are excluded.
The scalar tail executes its multiply/FMA even when it later uses division;
discarding that value does not discard its exception flags.

## Evidence chain

1. The unchanged `div3_tight.h` is compiled through `certified_div3.c` with
   Clang 19.1.5, `-O2 -mavx2 -mfma -ffp-contract=off -fno-fast-math
   -fno-vectorize -fno-slp-vectorize -fno-unroll-loops`.
2. An untrusted COFF extractor gathers the leaf and its five constants and
   resolves its RIP-relative relocations into a self-contained image.
3. Lean checks the complete observed byte list against the frozen image.
   `program_decoded` independently decodes opcode, VEX/register/address fields,
   displacements, and branch targets. It uses kernel reduction, not native
   decision. An altered compiler result is rejected; the script cannot update
   the semantic program to make an altered result pass.
4. `run_block` connects symbolic basic-block execution to the instruction
   interpreter. The block, counter, prefix-memory, and loop proofs compose to
   `machine_correct`. `Precondition` and `Postcondition` are in
   `lean/Div3Machine/Main.lean`; byte storage and aliasing are proved in
   `Memory.lean`, `Invariant.lean`, and `ChunkMemory.lean`.
5. The accepted image is assembled and linked. The native harness compares
   all 532 loaded bytes and the image extent before its first call, then runs
   the independent SoftFloat, mixed-lane, in-place, canary, and guard-page
   checks. Five byte mutations at opcode, branch, load, store, and constant
   sites must fail Lean acceptance.

The full linked-image sweep covers all 4,294,967,296 encodings in scalar and
SIMD execution, plus the hardware-division reference: 12,886,335,424 value
comparisons, zero mismatches, and 4,544 guard-page calls. These counts remain
empirical evidence; the quantified array and memory guarantees come from the
theorem. `results/machine_acceptance.json` records the exact image, source
hashes, counters, and rejected mutations. No new performance claim is made for
the dedicated ABI/compiler configuration.

## Explicit trust boundary

This is a proof relative to the small x86 instruction model in `ISA.lean` and
the primitive FP specifications in `Operations.lean`. It does not prove an
Intel processor, the operating system, loader, or external formal ISA/IEEE
specification correct. The handwritten decoder and instruction model still
need independent human review against the
[Intel instruction specification](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
Its omission of unused integer flags and FP exception state is deliberate;
the function does not branch on that omitted state. No compiler-correctness
premise appears in the theorem. Exact-image checking removes the compiler
from the proof's correctness dependencies, but the executable supplied to a
consumer must still be the checked image.

The primitive division premise is specifically division by the encoded
positive 3.0f; no specification for unused divisors is required.

All 54 source modules are replayed together without cached project proofs;
244 exported declarations are audited, including all 137 new machine-proof
theorems. The only permitted dependencies are the existing logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. This is not an independent
human audit or an algorithmic novelty claim.
