# Packet NT-CIRCLE — lattice points in discs and annuli; basic counting

Read `COMMON.md` (same directory) first.
Worktree: `/home/scott/WaveTurbulence-worktrees/nt-circle`, branch `w/nt-circle`.
Files you own: `WaveTurbulence/Foundations/NumberTheory/**`, `WaveTurbulence/Foundations/Counting/**`.

## Context

DH23 Lemma `basiccount0pre` (DH23 TeX `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`
L2028–L2050) bounds lattice points in an annulus using Huxley's exponent 7/11. Campaign scope (D1) is "everything
proved in Lean"; the orchestrator's analysis (`/home/scott/WaveTurbulence-dev/docs/FINDINGS.md`, F3) is that the
classical exponent 2/3 suffices for every use (DH23 L2051–L2117). This packet proves the 2/3 version.

## Goal (in this order; commit after each)

1. **Circle problem, exponent 2/3:** there is an absolute `C` with
   `|#{n ∈ ℤ² : ‖n − c‖ ≤ Q} − π Q²| ≤ C Q^{2/3}` for all `Q ≥ 1` and all centers `c ∈ ℝ²` (state with an
   explicit or existential absolute constant). Route: van der Corput's second-derivative test for
   `∑ ψ(f(n))` with `ψ(x) = x − ⌊x⌋ − 1/2`, or Sierpiński's argument. Check Mathlib and Scott's repos (KAM-dev,
   eth-constants, Frohlich-Spencer, Balaban) for exponential-sum or lattice-counting code first.
2. **Annulus bound** = DH23 `basiccount0pre` (1) with `Q^{7/11}` replaced by `Q^{2/3}`: for `A` the intersection of
   the annulus of radius `Q`, width `ρ` (with `Q⁻¹ ≤ ρ ≤ Q`; state the source's `≪` as explicit inequalities you
   need) and a disc of radius `L`: `#(A ∩ ℤ²) ≤ C·min(Qρ + Q^{2/3}, (Qρ)^{1/2} + L(Qρ)^{3/2}Q^{-1} + L(Qρ)^{1/2}Q^{-1/3})`.
   The second bound is elementary (L2037–L2040: no three non-collinear lattice points in a small convex set).
3. DH23 `basiccount0pre` (2) (`estcross`, L2032–L2050).
4. Report: the exact statements proved, and whether the 2/3 exponent visibly suffices at the uses L2076–L2117 (redo
   the "easy calculations" there with 2/3 and write them out in your handoff).

Map: `/home/scott/wave-turbulence/maps/DH23.md` (Appendix A entries).

## Stop conditions

Done: `READY nt-circle`. Blocked > ~1 hour on one ingredient: `STOPPED nt-circle: <reason>` with a proposed route.
