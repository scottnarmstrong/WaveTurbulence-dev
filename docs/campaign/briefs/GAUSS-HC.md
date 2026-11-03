# Packet GAUSS-HC — Gaussian hypercontractivity and large deviations

Read `COMMON.md` (same directory) first.
Worktree: `/home/scott/WaveTurbulence-worktrees/gauss-hc`, branch `w/gauss-hc`.
Files you own: `WaveTurbulence/Foundations/Gaussian/**` except `ComplexGaussian.lean` and `Isserlis*.lean`
(owned by packet CUMUL; you may import them once landed — until then put what you need in your own files under
distinct names and the orchestrator will reconcile).

## Goal

A sorry-free Lean proof of **DH21 Lemma A.3** (`largedev`, DH21 TeX
`/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` L2808–L2813), Gaussian
hypercontractivity for the centered normalized complex Gaussian family, and the large-deviation corollaries used in
DH21 Props 12.1–12.2 (L2707–L2756), DH21-2 Prop 4.8 (Sec 8.2), and TARGET Prop `fixedpoint` (TARGET L780–L794,
Section 12, L2306–L2339). See the maps `/home/scott/wave-turbulence/maps/DH21.md` (entries DH21-largedev,
DH21-finprop1, DH21-finprop2, DH212-mainprop2) and `T-part2.md` (Section 12).

Statement shape (adapt carriers; keep the constant exactly `(q-1)^{nq/2}`): for an iid family `η : ι → Ω → ℂ`
with law `stdComplexGaussian` (DRAFT below), signs `ζ : Fin n → Bool` (or `ℤˣ`), and a finitely supported coefficient
array `a : (Fin n → ι) → ℂ`, the random variable `X = ∑ a(k) ∏_j η_{k_j}^{ζ_j}` (`z^+ = z`, `z^- = conj z`)
satisfies, for all real `q ≥ 2`, `𝔼|X|^q ≤ (q-1)^{nq/2} (𝔼|X|²)^{q/2}`. Then the tail corollary
`P(|X| ≥ λ (𝔼|X|²)^{1/2}) ≤ C exp(-c λ^{2/n})` (state with explicit constants), and the version for the countable
L²-convergent sums DH21 uses (coefficients summable over `ℤ_L^d`), if needed by DH21 Prop 12.1.

Expected route: Nelson's hypercontractivity of the Ornstein–Uhlenbeck semigroup on finite-dimensional real Gaussian
space (Gross log-Sobolev + tensorization, or Bonami–Beckner two-point inequality + CLT, or Mehler kernel), applied to
the real and imaginary parts (`η = (ξ₁ + i ξ₂)/√2`), plus the fact that `X` has degree ≤ n in the real Gaussians
(so `‖T_t⁻¹ X‖₂ ≤ e^{nt}‖X‖₂`). Before building: mine RegularityStructures-dev, GlobalPhi43-dev, Critical2DKPZ,
DOZZ, Balaban (search for hypercontractivity, Mehler, Ornstein–Uhlenbeck, log-Sobolev, Wiener chaos, equivalence of
moments) and Mathlib (`ProbabilityTheory.gaussianReal`, `IsGaussian`, `Measure.infinitePi`). Report what you found.

## DRAFT definition (copy verbatim into `WaveTurbulence/Foundations/Gaussian/StdComplexGaussianDraft.lean` only if
CUMUL has not landed `ComplexGaussian.lean` yet)

```lean
/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm
```
(namespace `WaveTurbulence`, `open MeasureTheory ProbabilityTheory`.)

## Stop conditions

Done: `READY gauss-hc` with the main theorem names. Blocked for more than ~1 hour on one missing ingredient: write
what is missing and propose a route, then `STOPPED gauss-hc: <reason>`.
