# Packet NT2 HUA — Hua's inequality, the shared Weyl-sum reduction, L^{3d/2} moments of Weyl sums

Read `COMMON.md` first. Blueprint rows `DH21.hua`, `NT.weylReduction`, `NT.weylMoment` (packet NT2) in
`/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`. Same worktree (`/home/scott/WaveTurbulence-worktrees/gausssum`);
new branch `git switch -c w/hua main`. Files: `WaveTurbulence/Foundations/WeylSums/**` (namespace
`WaveTurbulence.WeylSums`), building on your landed GAUSSSUM modules; the landed `Foundations/Fourier/**` (χ₀, Gevrey,
time-Fourier norms; wt-anfourier) and `Foundations/NumberTheory/**` (Poisson/stationary phase pieces; wt-nt) may be
imported, not edited.

Goals (commit after each):
1. **DH21.hua** (DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` L2823–L2833,
   Lemma A.5): `‖G_h(·,r,n)‖⁴_{L⁴[0,1]} ≲ n² log(2+n)` and `‖G_h‖⁶_{L⁶} ≲ n⁴`, uniformly in (r,h), where G_h is the
   quadratic Weyl sum of your GAUSSSUM packet (counting solutions of a²−b²+c²−d²=0 with divisor/gcd sums).
2. **NT.weylReduction** (DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` L1076–L1136;
   TARGET L1560): the "standard reductions" of DH23 Lemma 6.6: sums over x, y (, z) ∈ ℤ_L^d of products of shifted
   cutoffs times e(quadratic phase) reduced to products of one-dimensional Weyl sums, with compactly supported
   replacements of χ̂₀ and shifted linear frequencies. State it generically (any Gevrey/compactly supported cutoff).
3. **NT.weylMoment** (TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L1567–L1590):
   `∫_0^1 |G(t′)|^{3d/2} dt′ ≲ L^{3d/2−2}` for 3d/2 > 4, and the localized major-arc variant
   `≲ L^{3d/2−2+(2γ−2)}` (read the source for exact forms; constants may depend on (d,γ,η)).
Done: `READY hua`.
