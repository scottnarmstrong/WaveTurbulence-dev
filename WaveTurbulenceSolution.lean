/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
import WaveTurbulence.Frozen.Theorems.Main

/-!
# Theorem 1.1 of Deng–Hani: the comparator solution

This file repeats the declarations of `WaveTurbulenceChallenge.lean` verbatim (only this docstring,
the imports and the proof differ) and proves `main` from `WaveTurbulence.main`
(`WaveTurbulence/Frozen/Theorems/Main.lean`), of which it is a definitional restatement: the twelve
definitions below are verbatim copies of those of `WaveTurbulence/Frozen/Defs/`.

The Challenge is a standalone, Mathlib-only statement of Theorem 1.1 of Y. Deng and Z. Hani,
*Long time justification of wave turbulence theory* (arXiv:2311.10082v2), in the case `0 < γ < 1`
on the square torus `𝕋_L^d = (ℝ / Lℤ)^d`, `d ≥ 3`. "DH" below is this paper; equation tags such as
(WKE), (NLS) and (DAT) are its own.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulenceChallenge

/-- Momentum space `ℝ^d` with the Euclidean inner product `⟨k, ℓ⟩ = ∑ kʲ ℓʲ` (DH (COL), §1.1). -/
abbrev Mom (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The lattice point `k = n / L ∈ ℤ_L^d = (L⁻¹ ℤ)^d` of the dual torus (DH §1.1). -/
def latticePoint {d : ℕ} (L : ℝ) (n : Fin d → ℤ) : Mom d :=
  WithLp.toLp 2 (fun j => (n j : ℝ) / L)

/-- The cubic collision operator `𝒦(φ₁, φ₂, φ₃)(k)` of (COL), written after the change of
variables `k₁ = k + ℓ₁`, `k₃ = k + ℓ₃`, `k₂ = k + ℓ₁ + ℓ₃` of (C.5) (which removes the first
delta and turns the second into `δ(-2⟨ℓ₁, ℓ₃⟩)`), with `∫ g(ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₃ =
(2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} g`, the integral over the hyperplane `ℓ₁^⊥` taken against its
`(d-1)`-dimensional Lebesgue measure. -/
def collisionOp {d : ℕ} (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ₁ : Mom d, (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ,
    (φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      - φ₁ k * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + w)
      - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ k)

/-- `φ` is a Schwartz-class solution of (WKE) on `[0, τ★]` with initial data `φin`:
`τ ↦ φ τ` is continuous on `[0, τ★]` into the Schwartz space, `φ 0 = φin`, and
`∂_τ φ(τ, k) = 𝒦(φ(τ), φ(τ), φ(τ))(k)` for every `τ ∈ [0, τ★]` and `k ∈ ℝ^d`
(one-sided at the endpoints). -/
def IsWKESolution {d : ℕ} (φin : 𝓢(Mom d, ℝ)) (τstar : ℝ) (φ : ℝ → 𝓢(Mom d, ℝ)) : Prop :=
  ContinuousOn φ (Icc 0 τstar) ∧ φ 0 = φin ∧
    ∀ τ ∈ Icc 0 τstar, ∀ k : Mom d,
      HasDerivWithinAt (fun s => φ s k) (collisionOp (φ τ) (φ τ) (φ τ) k) (Icc 0 τstar) τ

/-- The partial derivative `∂_{x_j} f(x)`. -/
def partialDeriv {d : ℕ} (j : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  deriv (fun r : ℝ => f (Function.update x j r)) (x j)

/-- The normalized Laplacian `Δ = (2π)⁻¹ (∂²_{x_1} + ⋯ + ∂²_{x_d})` of DH §1.1. -/
def normLaplacian {d : ℕ} (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∑ j, partialDeriv j (partialDeriv j f) x

/-- The space Fourier coefficient (DH (1.2)):
`f̂(k) = L^{-d/2} ∫_{[0,L]^d} f(x) e^{-2πi k·x} dx` at `k = n / L ∈ ℤ_L^d`. -/
def torusFourierCoeff {d : ℕ} (L : ℝ) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
      f x * exp (-(2 * Real.pi * ∑ j, (n j : ℝ) / L * x j : ℝ) * I)

/-- `u` is a smooth solution on `[0, T]` of (NLS) `(i∂_t - Δ)u + α|u|²u = 0` on `𝕋_L^d`,
whose initial datum `u(0, ·)` has Fourier coefficients `û(0, n/L) = c n`: `u` is `C^∞` on
`[0, T] × ℝ^d`, `L`-periodic in each space variable, and satisfies the equation pointwise
(one-sided time derivative at `t = 0, T`). -/
def IsSmoothNLSSolution {d : ℕ} (L α T : ℝ) (c : (Fin d → ℤ) → ℂ)
    (u : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2) (Icc 0 T ×ˢ univ) ∧
    (∀ t ∈ Icc 0 T, ∀ x : Fin d → ℝ, ∀ j : Fin d, u t (x + Pi.single j L) = u t x) ∧
    (∀ n : Fin d → ℤ, torusFourierCoeff L (u 0) n = c n) ∧
    ∀ t ∈ Icc 0 T, ∀ x : Fin d → ℝ,
      I * derivWithin (fun s => u s x) (Icc 0 T) t - normLaplacian (u t) x
        + (α : ℂ) * ((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x = 0

/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm

/-- The Fourier coefficients `û_in(k) = √(φin(k)) g_k` of the random initial datum (DAT). -/
def initialCoeff {d : ℕ} {Ω : Type*} (L : ℝ) (φin : Mom d → ℝ) (g : (Fin d → ℤ) → Ω → ℂ)
    (ω : Ω) (n : Fin d → ℤ) : ℂ :=
  (Real.sqrt (φin (latticePoint L n)) : ℂ) * g n ω

/-- The event that (NLS) with data (DAT) has a smooth solution on `[0, T]`. -/
def solvableEvent {d : ℕ} {Ω : Type*} (L α T : ℝ) (φin : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) : Set Ω :=
  {ω | ∃ u, IsSmoothNLSSolution L α T (initialCoeff L φin g ω) u}

/-- The kinetic (Van Hove) time `T_kin = 1 / (2α²)` (DH §1.1, L297). -/
def kineticTime (α : ℝ) : ℝ := 1 / (2 * α ^ 2)

universe u

/-- **Deng–Hani, Theorem 1.1** (case `0 < γ < 1`, square torus). -/
theorem main (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ θ > (0 : ℝ), ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) →
      ∀ τstar > (0 : ℝ), ∀ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ →
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
        MeasurableSet (solvableEvent L α T φin g) ∧
        1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ P.real (solvableEvent L α T φin g) ∧
        ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
          (∀ ω ∈ solvableEvent L α T φin g,
            IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)) →
          ∀ t ∈ Icc 0 T, ∀ n : Fin d → ℤ,
            |(∫ ω, (solvableEvent L α T φin g).indicator
                  (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω ∂P)
              - φ (t / kineticTime α) (latticePoint L n)| ≤ L ^ (-θ) := by
  exact _root_.WaveTurbulence.main d hd γ hγ

end WaveTurbulenceChallenge
