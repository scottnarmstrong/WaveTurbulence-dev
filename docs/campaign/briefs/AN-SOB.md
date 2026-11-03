# Packet N4 AN-SOB — Sobolev/Morrey inequalities, simplex volumes, DH21 (10.5), DH21 Lemma 10.2

Read `COMMON.md` (same directory) first. Blueprint: `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`
(rows AN.sobolev, AN.simplexVol, DH21.elemineq, DH21.timeintlemma; packet N4).
Worktree: `/home/scott/WaveTurbulence-worktrees/an-sob`, branch `w/an-sob`.
Files you own: `WaveTurbulence/Foundations/Analysis/**`.

## Goals (in this order; commit after each)

1. **AN.sobolev** (TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L998, L2314,
   L2330): (a) weighted `W^{d,1}(ℝ^d) ⊂ L^∞` as used in (incohproof4) L998; (b) `H¹([p,p+1]) ⊂ L^∞`: for `C¹` `f`
   on an interval of length 1, `sup |f| ≤ C(‖f‖_{L²} + ‖f′‖_{L²})` (sobolev) L2314–L2316, also the vector-valued /
   ℓ²-in-k version used there (sup over k ∈ ℤ_L^d and t of |f_k(t)| bounded by the L²_{k,t} norms of f and ∂_t f);
   (c) the Gagliardo–Nirenberg/Morrey bound (sobolev2) L2330 on the unit square in (t,s):
   `sup |K|^{2P} ≤ M^{P/100}‖K‖_{L^{2P}}^{2P} + M^{-100P}‖∂_{t,s}K‖_{L^{2P}}^{2P}` — state precisely what is true
   (constants, range of P, M ≥ 1) and prove it.
2. **AN.simplexVol** (T L2029–L2036): volumes of heap-ordered simplices in a tree order (number of linear extensions
   / volume of `{t : t_child < t_parent}` in `[0,1]^n`), volumes of two interleaved monotone sequences in `[0,𝔇]^z`,
   and the elementary bound `x^z/(z−d)! ≤ x^d e^x`.
3. **DH21.elemineq** (DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
   L2428, eq. (10.5)): `sup_{[0,1]^n}|F| ≤ ∑_{A ⊆ [n]} ∫_{[0,1]^n} |∏_{v∈A}(∂_{α_v} − πi𝔏_v)F|` for smooth F (read the
   source for the exact form).
4. **DH21.timeintlemma** (DH21 L2432–L2451, Lemma 10.2, which cites DH19 Prop 2.3 —
   `/home/scott/wave-turbulence/references/src-1912.09518/Derivation-of-WKE-11.tex`, around L347–L407): the bound
   `|U_T(t,σ,α[𝒩])| ≤ C^n ∑_{d∈{0,1}^𝒩} ∏_𝔫 ⟨q_𝔫⟩^{-1}` for iterated oscillatory time integrals over heap-ordered
   domains of a ternary tree. Here trees are needed: use a minimal local representation (e.g. a finite rooted forest
   given by a parent map on `Fin n`) with a clear docstring; the combinatorial carriers will be frozen later (Wave B)
   and you will then add a bridge. Report the exact statement you proved.

## Stop conditions
Done: `READY an-sob`. Blocked > ~1 hour on one ingredient: `STOPPED an-sob: <reason>` with a proposed route.
