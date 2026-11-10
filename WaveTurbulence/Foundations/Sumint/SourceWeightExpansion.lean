/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.FiniteWeightExpansion
public import WaveTurbulence.Foundations.Sumint.ExponentMargins
import Mathlib.Tactic

/-!
# Fourier mass of the exact primary and alternative source weights

The two families use their drafted regularity orders without alteration.
Their coefficient masses contain the full source factor
`L^{- (γ₁-√η) M₁}` before reserving decay for bad blocks.
-/

public section

open MeasureTheory Finset
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Sumint

/-- The two weight families, before composition with any affine map. -/
@[expose] noncomputable def sourceWeight {d : ℕ} (D : SumintDatum d) :
    D.S.VIdx ⊕ D.S.VIdx → Mom d → ℂ := Sum.elim D.wK D.wL

/-- Their exact drafted spatial weights. -/
@[expose] def sourceWeightOrder {d : ℕ} (D : SumintDatum d) : D.S.VIdx ⊕ D.S.VIdx → ℕ :=
  Sum.elim (fun _ => 30 * d) (fun _ => 0)

/-- Multiplicity of the decay exponent at each source weight. -/
@[expose] def sourceWeightMultiplicity {d : ℕ} (D : SumintDatum d) : D.S.VIdx ⊕ D.S.VIdx → ℕ :=
  Sum.elim D.g D.g'

/-- Total multiplicity agrees exactly with the draft's `M₁`. -/
theorem sum_sourceWeightMultiplicity {d : ℕ} (D : SumintDatum d) :
    ∑ i, sourceWeightMultiplicity D i = D.M₁ := by
  simp [sourceWeightMultiplicity, SumintDatum.M₁, Fintype.sum_sum_type, Finset.sum_add_distrib]

/-- Exact source weight bounds, bundled without losing the alternative family's order zero. -/
theorem sourceWeight_bound {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps) (i : D.S.VIdx ⊕ D.S.VIdx) :
    SNorm (30 * d) (sourceWeightOrder D i) (sourceWeight D i) ≤
      ENNReal.ofReal (L ^ (-(gammaWeight d γ - Real.sqrt η) * sourceWeightMultiplicity D i)) := by
  cases i with
  | inl v => exact (hD.2.2.2.2.1 v).1
  | inr v => exact (hD.2.2.2.2.1 v).2

/-- The product of the scalar decay factors is the literal total decay in the source proof. -/
theorem prod_source_decay {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (s : ℝ) :
    (∏ i, L ^ (-s * (sourceWeightMultiplicity D i : ℝ))) = L ^ (-s * D.M₁) := by
  rw [← Real.rpow_sum_of_pos hL]
  congr 1
  rw [← Finset.mul_sum, ← Nat.cast_sum, sum_sourceWeightMultiplicity]

/-- The exact source families have integrable tensor Fourier coefficients. -/
theorem source_tensor_fourier_integrable {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx ⊕ D.S.VIdx → Fin d → ℤ) :
    Integrable (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      ∏ i, 𝓕 (localizedWeight (a i) (sourceWeight D i)) (ξ i)) := by
  apply integrable_tensor_localized_fourier (N := 30 * d) (by omega) (by omega)
    (sourceWeightOrder D) (sourceWeight D)
    (fun i => L ^ (-(gammaWeight d γ - Real.sqrt η) * sourceWeightMultiplicity D i))
  · intro i
    exact Real.rpow_nonneg hL.le _
  · exact sourceWeight_bound D hD

/-- Literal simultaneous modulation expansion at the draft's primary and alternative affine maps. -/
theorem source_localized_weights_expansion {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) :
    (∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
      ∏ i, (Real.fourierChar (inner ℝ (ξ i) (Sum.elim (D.kVec L x E) (D.ℓVec L x E) i)) : ℂ) *
        𝓕 (localizedWeight (Sum.elim a b i) (sourceWeight D i)) (ξ i)) =
      ∏ v, localizedWeight (a v) (D.wK v) (D.kVec L x E v) *
        localizedWeight (b v) (D.wL v) (D.ℓVec L x E v) := by
  have h := finite_localizedWeight_expansion (N := 30 * d) (by omega) (by omega)
    (sourceWeightOrder D) (sourceWeight D)
    (fun i => L ^ (-(gammaWeight d γ - Real.sqrt η) * sourceWeightMultiplicity D i))
    (fun _ => Real.rpow_nonneg hL.le _) (sourceWeight_bound D hD)
    (Sum.elim a b) (Sum.elim (D.kVec L x E) (D.ℓVec L x E))
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, sourceWeight,
    Finset.prod_mul_distrib] using h

end WaveTurbulence.Sumint
