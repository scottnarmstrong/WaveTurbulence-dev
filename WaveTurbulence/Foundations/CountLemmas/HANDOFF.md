# COUNT handoff

Branch `w/count`; implementation milestone `f97dc2c`, followed by merge
`8f5c31b` of main `99bff87`. All packet files are under
`WaveTurbulence/Foundations/CountLemmas/`. No frozen anchors or root imports
were edited by this packet. Import `CountTools.lean` for the complete interface.

## Results and files

- `AtomCount.lean`: `atomCountLemma_bound`, exactly the audited B1.8 draft.
- `CountLemma.lean`: `countLemma_bound`, exactly the audited B1.7 draft.
- `DH23Second.lean`: `dh23_second_pair_bound`, the supplementary DH23 A.2(2)
  estimate, for every selector, with explicit sufficiently small eta.
- `CoupledSets`, `AtomSets`, strip/shell/fiber modules: concrete finite lattice
  sets and elementary geometric reductions.
- `Star*`, `FullStar*`, `Triple*`: positive double-band Fourier majorant,
  full-square cubic-star moments, and the three triple selectors.
- `Pair*`, `LowPair*`, `HighPair*`, `Radial*`, `*Growth`, `PowerAbsorption`:
  pair counting, radial summation, and uniform power/threshold bookkeeping.
- `DyadicDensity`, `PairFiberCap`, `PairWeakDensity`, `WeakPair*`, `SecondPair*`:
  weighted density distribution and the individual-selector supplementary bound.
- `Improved*`: annulus threshold and fixed-sum fibers using the unconditional
  VdCB circle exponent 27/41.
- `CountTools.lean`: public import interface. There are 95 Lean files, each
  at most 121 lines; the directory itself is the full file inventory.

## Approach

For atom pairs, complete the square for equal signs and count a planar shell,
then lift the remaining coordinates. Opposite signs use a dominant coordinate
of the nonzero conserved difference and a linear strip. The triple atom estimate
uses the previously proved conserved three-vector bound.

For coupled triples, the star selector uses a positive tensor Fourier kernel,
a scaled plateau cutoff and the full-square cubic-star integral. Separate
nonzero/nonzero, nonzero/zero and zero/zero moments preserve the log-free term
at gamma=1/2. The sum selectors project to the sum and third vector, then apply
a bilinear-band estimate and a positive atom fiber bound.

For coupled pairs at gamma at most 1/2, radial summation and an independent
strip give the exact reciprocal gain, combined with the baseline for the cap.
Above 1/2, split small radius from sparse/dense fibers; polynomial growth absorbs
fixed constants and logarithms into the large-L threshold, uniformly in centers
and P, with delta fixed. Sum selectors use planar annuli. The exact draft is
independent of eta, so its existential eta0 can be chosen as 1.

The supplementary A.2(2) estimate uses a dyadic sum over actual fiber sizes,
retaining a linear density threshold. For the sum selector, the unconditional
27/41 discrepancy bound yields the fiber exponent 81*(2+a)/244 when squared
energy width is at most L^a. The explicit choice
`secondPairEta0 gamma = min ((1-gamma)/10000) (1/1000000)` supplies the strict
margins under gamma > 4/5 - 10 eta. Fixed delta affects only the threshold;
the stated outside constant can be 1 after increasing that threshold.

## Checks

After merging main:

```
nice -n 5 lake build WaveTurbulence.Foundations.CountLemmas.CountTools
Build completed successfully (9450 jobs).

nice -n 5 lake env lean /home/scott/wt-scratch/count/FinalAxioms.lean
'WaveTurbulence.CountLemmas.atomCountLemma_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.CountLemmas.countLemma_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.CountLemmas.dh23_second_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both exit 0. Earlier targeted AtomCount, CountLemma, SecondPairX and
SecondPairSum builds also passed. No whole-library build or Mathlib rebuild.

Whitespace-normalized declarations compared against
`/home/scott/wt-scratch/waveb-snap-5/WaveB1-Statements.lean`:

```
atomCountLemma: exact draft statement comparison PASS (declaration name only changed)
countLemma: exact draft statement comparison PASS (declaration name only changed)
```

All 95 owned Lean files passed module-shape and 1500-line checks (maximum 121),
forbidden-token scan (no sorry/axiom/admit/unsafe/opaque), and duplicate declaration
short-name scan (none). `git diff --check` passed.

The requested MINOR-ARCS duplicate repair is already committed on
`w/minor-arcs` as `5f6afcc`: WeightedDiagonalScale imports WeightedDiagonalBound
and uses its single public `weightedDiagonalAmplitude_support`. Both affected
modules were rebuilt successfully. This repair is included in this branch.

## Errata, deviations and uncertainties

New suspected source typo: DH23 `Revision_Submit.tex` line 2110 prints
`|k_1|^2-|k_2|^2+|k_3|^2-|k|^2=2(k_1-k)\\cdot(k_3-k)` under
`k_1-k_2+k_3=k`. The correct factor is **-2**. For example k1=k3=1,
k2=0, k=2 gives left side -2 and printed right side +2; embed in the first
coordinate for d>=3. The proved conserved-energy identity uses the correct
sign. This only reverses the arbitrary energy center in the counting argument.

Existing rulings retained: F43 excludes k=0 in the opposite-sign atom bound;
Q8b interprets the strengthened atom parameter as the conserved difference;
F31 uses the corrected elementary branch in the DH23 pair proof. The exact
draft statements are unchanged. The supplementary estimate replaces Huxley's
input with the proved 27/41 circle theorem, with explicit smallness of eta.
It needs only the lower norm comparison for P (a stronger result than assuming
both comparisons). No black boxes, conclusion-shaped premises or additional
axioms are used. No remaining mathematical uncertainties or unfinished goals.

READY count
