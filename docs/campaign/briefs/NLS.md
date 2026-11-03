# Packet NLS — smooth solutions of cubic NLS on 𝕋_L^d and the reduction to the a_k system

Read `COMMON.md` (same directory) first. Builds on the landed `WaveTurbulence/Foundations/Torus/**` (your
TORUS-FOURIER packet) and the frozen definitions (D6).
Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier`, new branch: `git switch -c w/nls main` (after your
previous branch landed as 5beb902). Files you own: `WaveTurbulence/Foundations/NLS/**`.

## Sources

TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`: (NLS) L278–L283, (DAT) L290–L294,
Theorem 1.1 L314–L320, first reduction L540–L566 ((reducedcoef), (akeqn), (akeqn2), (defcoef0), (res), (defset)),
gauge/translation invariance (gaugeinv) L567–L570, proof of Theorem 1.1 L795–L823 (mass-conservation step at
L818–L820). Map: `/home/scott/wave-turbulence/maps/T-part1.md` (NLS → a-system reduction entry; open questions Q2, Q4
= FINDINGS F6, F8). Frozen: `IsSmoothNLSSolution`, `solvableEvent`, `initialCoeff`, `torusFourierCoeff`,
`normLaplacian`, `partialDeriv`, `kineticTime`, `stdComplexGaussian`.

## Goals (in this order; commit after each)

1. **Fourier-side equation.** For `u` with `IsSmoothNLSSolution L α T c u` (L > 0), `t ↦ û(t,n)` satisfies on `[0,T]`
   the ODE obtained from (NLS) by your coefficient formulas (Laplacian multiplier and cubic convolution with the
   `L^{-d}`-type factor) — state it exactly.
2. **Uniqueness** of smooth periodic solutions on `[0,T]` with the same data (L² energy estimate + Gronwall). Corollary:
   for ω in `solvableEvent`, any two selections `U ω` agree on `[0,T] × ℝ^d`.
3. **Mass conservation**: `∫_{[0,L]^d} |u(t)|² = ∫ |u(0)|²`, equivalently `∑_n |û(t,n)|² = ∑_n |c n|²`.
4. **Reduction to the a_k system** (L540–L566): for `M = ⨍|u|²`, `v = e^{-2iαMt}u` solves the Wick-ordered equation;
   `a_k(t)` defined by (reducedcoef) with `α = L^{-γ}`, `T_kin = kineticTime α`, rescaled time `t ∈ [0, 𝔇]`
   (`𝔇 δ = τ★`), solves (akeqn)–(akeqn2) with `ε_{k₁k₂k₃}` of (defcoef0) and `Ω` of (res). State the equivalence
   precisely in both directions: (⇒) smooth NLS solution ⇒ a-system solution; (⇐) an a-system solution on `[0, 𝔇]`
   whose coefficients decay rapidly (uniformly in t) gives a smooth NLS solution on `[0, T]` (inverse gauge: note
   that the mass is conserved, so the gauge factor is computable from the data).
5. **Persistence of regularity / local theory** in `H^s(𝕋_L^d)`, `s > d/2` (algebra property): local existence with
   time depending on the `H^s` norm, uniqueness, blow-up alternative, and persistence of all higher `H^{s'}` norms. This
   is what turns the paper's a-system solution with polynomial decay into a C^∞ solution (FINDINGS F8), and it is the
   route to goal 6.
6. **Measurability** (needed for the frozen conjunct `MeasurableSet (solvableEvent …)` and for the integrand of
   Theorem 1.1, D6): for measurable `g`, `solvableEvent L α T φin g` is a measurable set and
   `ω ↦ indicator(F) |û(U ω t, n)|²` is (a.e.-)measurable for any selection `U` as in the frozen theorem; plus the
   integrability bound from mass conservation `|û(t,n)|² ≤ ∑_m φin(m/L) |g_m|²` (L818–L820).
7. **Symmetries**: gauge (`u ↦ e^{iθ}u`) and space translation invariance of the solution map and of `solvableEvent`,
   in the form TARGET (gaugeinv) uses.

Mine Scott's repos for NLS / Schrödinger / energy-estimate code first (NavierStokesAndEuler, Superdiffusion,
EscauriazaSereginSverak, CaffarelliKohnNirenberg) and Mathlib.

## Stop conditions

Done: `READY nls`. Blocked > ~1 hour on one ingredient: `STOPPED nls: <reason>` with a proposed route.
