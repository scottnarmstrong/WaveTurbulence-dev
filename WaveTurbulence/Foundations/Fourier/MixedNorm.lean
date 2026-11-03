/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Weighted Fourier norms with momentum derivatives

TARGET `(normX)` and `(normX2)`, L581–L585, and `(locnorm)`, L589.
The supremum over derivative words of length at most `Λ₁` implements the
maximum over coordinate multiindices. On `C^{Λ₁}` inputs the order of
coordinate differentiation does not matter. Momentum suprema are pointwise,
as specified in WAVE-B §2.6. All norms are extended nonnegative reals.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- The Euclidean Japanese bracket in momentum space. -/
@[expose] noncomputable def momentumBracket {d : ℕ} (k : Mom d) : ℝ :=
  Real.sqrt (1 + ‖k‖ ^ 2)

/-- A coordinate word applied to the iterated Fréchet derivative. -/
@[expose] noncomputable def momentumDerivative {d n : ℕ}
    (ρ : Fin n → Fin d) (f : Mom d → ℂ) (k : Mom d) : ℂ :=
  iteratedFDeriv ℝ n f k (fun i => EuclideanSpace.single (ρ i) 1)

/-- The weighted pointwise supremum of a momentum function. -/
@[expose] noncomputable def momentumSupNorm {d : ℕ} (Λ : ℕ)
    (f : Mom d → ℂ) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (momentumBracket k ^ Λ) * ‖f k‖ₑ

/-- TARGET `(normX2)`. Nonsmooth inputs have value infinity. -/
@[expose] noncomputable def spatialNorm {d : ℕ} (Λ₁ Λ₂ : ℕ)
    (f : Mom d → ℂ) : ℝ≥0∞ := by
  classical
  exact if ContDiff ℝ Λ₁ f then
    ⨆ (n : ℕ) (_ : n ≤ Λ₁) (ρ : Fin n → Fin d),
      momentumSupNorm Λ₂ (momentumDerivative ρ f)
  else ⊤

/-- The time Fourier transform with momentum held fixed. -/
@[expose] noncomputable def mixedTimeFourier {r d : ℕ}
    (F : (Fin r → ℝ) → Mom d → ℂ) (ξ : Fin r → ℝ) (k : Mom d) : ℂ :=
  timeFourier (fun t => F t k) ξ

/-- The defining admissibility condition for TARGET `(normX)`, as ruled in
WAVE-B §2.6: integrable time slices and almost-everywhere smooth transformed
momentum slices. Failure gives infinity rather than a junk integral. -/
@[expose] def MixedFourierAdmissible {r d : ℕ} (Λ₁ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) : Prop :=
  (∀ k, Integrable (fun t => F t k)) ∧
    (∀ᵐ ξ, ContDiff ℝ Λ₁ (mixedTimeFourier F ξ))

/-- TARGET `(normX)`, L581: the momentum supremum is inside the frequency
integral, and the derivative supremum is outside it. -/
@[expose] noncomputable def mixedFourierNorm {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ := by
  classical
  exact if MixedFourierAdmissible Λ₁ F then
    ⨆ (n : ℕ) (_ : n ≤ Λ₁) (ρ : Fin n → Fin d),
      ∫⁻ ξ, timeWeight θ ξ *
        momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier F ξ))
  else ⊤

/-- TARGET `(locnorm)`, allowing any set `K` of momentum arguments. In
particular `K` can be a lattice or a lattice coset. -/
@[expose] noncomputable def mixedRestrictionNorm {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : B → K → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → Mom d → ℂ)
    (_ : ∀ (t : B) (k : K), G t k = F t k), mixedFourierNorm θ Λ₁ Λ₂ G

/-- Restriction of `(normX2)` to an arbitrary set of momenta. -/
@[expose] noncomputable def spatialRestrictionNorm {d : ℕ} (Λ₁ Λ₂ : ℕ)
    (K : Set (Mom d)) (f : K → ℂ) : ℝ≥0∞ :=
  ⨅ (g : Mom d → ℂ) (_ : ∀ k : K, g k = f k), spatialNorm Λ₁ Λ₂ g

theorem mixedFourierNorm_of_not_admissible {r d : ℕ} {θ : ℝ} {Λ₁ Λ₂ : ℕ}
    {F : (Fin r → ℝ) → Mom d → ℂ} (hF : ¬ MixedFourierAdmissible Λ₁ F) :
    mixedFourierNorm θ Λ₁ Λ₂ F = ⊤ := by
  simp [mixedFourierNorm, hF]

theorem mixedRestrictionNorm_le_extension {r d : ℕ} {θ : ℝ} {Λ₁ Λ₂ : ℕ}
    {B : Set (Fin r → ℝ)} {K : Set (Mom d)} {F : B → K → ℂ}
    (G : (Fin r → ℝ) → Mom d → ℂ)
    (hG : ∀ (t : B) (k : K), G t k = F t k) :
    mixedRestrictionNorm θ Λ₁ Λ₂ B K F ≤ mixedFourierNorm θ Λ₁ Λ₂ G :=
  iInf_le_of_le G (iInf_le_of_le hG le_rfl)

theorem spatialRestrictionNorm_le_extension {d : ℕ} {Λ₁ Λ₂ : ℕ}
    {K : Set (Mom d)} {f : K → ℂ} (g : Mom d → ℂ) (hg : ∀ k : K, g k = f k) :
    spatialRestrictionNorm Λ₁ Λ₂ K f ≤ spatialNorm Λ₁ Λ₂ g :=
  iInf_le_of_le g (iInf_le_of_le hg le_rfl)

end WaveTurbulence.Fourier
