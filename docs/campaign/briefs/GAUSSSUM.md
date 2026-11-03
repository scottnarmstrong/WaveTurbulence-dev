# Packet NT1 GAUSSSUM — Dirichlet approximation and quadratic Weyl (Gauss) sum bounds

Read `COMMON.md` (same directory) first. Blueprint: `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`
(rows NT.dirichlet, NT.gaussSum; packet NT1; consumers DH23.minorarcs2, NT.weylMoment, T.lemcubic).
Worktree: `/home/scott/WaveTurbulence-worktrees/gausssum`, branch `w/gausssum`.
Files you own: `WaveTurbulence/Foundations/WeylSums/**` (coordinate by name with NT-CIRCLE, which owns
`Foundations/NumberTheory/**` and `Foundations/Counting/**`; do not edit those).

## Goals (in this order; commit after each)

1. **NT.dirichlet**: Dirichlet approximation in the form used (for real t and K ≥ 1 there are coprime a, q with
   1 ≤ q ≤ K and |t − a/q| ≤ 1/(qK)); Mathlib has `Real.exists_rat_abs_sub_le_and_den_le` — wrap it.
2. **NT.gaussSum** (DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` L1100–L1136,
   the "Gauss lemma"; DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
   L1445 (GaussLem); TARGET L1564): for `|s − a/q| ≤ 1/(qK)`, `(a,q) = 1`, `q ≤ K`:
   `|∑_{p=h}^{h+K} e(s p² + r p)| ≲ K log K / (√q (1 + K|s − a/q|^{1/2}))`, uniformly in h, r; then the smooth-cutoff
   variant `sup_{h,ρ} |∑_x χ((x−h)/L) e(t′x² + ρx)|` with χ a smooth compactly supported cutoff (state the bound;
   use a generic `ContDiff` compactly supported χ, not a specific frozen cutoff). Standard route: Weyl differencing
   (squaring) + geometric series bound `min(K, ‖2sh‖⁻¹)` + counting with the rational approximation.
3. If time permits: DH21 Lemma A.5 (Hua's inequality, L⁴ and L⁶ moments of Weyl sums) — packet NT2 HUA — report
   before starting it.

Mine Mathlib (`Mathlib/NumberTheory/`, `ZMod`, Gauss sums in `Mathlib.NumberTheory.GaussSum`) and Scott's repos
(KAM-dev, eth-constants) first.

## Stop conditions
Done: `READY gausssum`. Blocked > ~1 hour on one ingredient: `STOPPED gausssum: <reason>` with a proposed route.
