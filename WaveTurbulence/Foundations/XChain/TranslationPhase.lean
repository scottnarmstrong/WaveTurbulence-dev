/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedGauge
/-! Spatial-translation phases and their exact cubic momentum character. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

noncomputable def translationPhase {d : ℕ} (L : ℝ) (x : Mom d) (n : Fin d → ℤ) : ℂ :=
  Complex.exp ((-(2 * Real.pi * inner ℝ (latticePoint L n) x) : ℝ) * Complex.I)

theorem norm_translationPhase {d : ℕ} (L : ℝ) (x : Mom d) (n : Fin d → ℤ) :
    ‖translationPhase L x n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem inv_translationPhase {d : ℕ} (L : ℝ) (x : Mom d) (n : Fin d → ℤ) :
    (translationPhase L x n)⁻¹ = translationPhase L (-x) n := by
  unfold translationPhase
  rw [← Complex.exp_neg]
  congr 1
  simp only [inner_neg_right, neg_mul, mul_neg, neg_neg, Complex.ofReal_neg]

theorem translation_phase_relation {d : ℕ} (L : ℝ) (x : Mom d) (n q₁ q₂ : Fin d → ℤ) :
    translationPhase L x q₁ * (starRingEnd ℂ) (translationPhase L x q₂) *
      translationPhase L x (n - q₁ + q₂) = translationPhase L x n := by
  have hk : latticePoint L (n - q₁ + q₂) = latticePoint L n - latticePoint L q₁ + latticePoint L q₂ := by
    ext j
    simp [latticePoint]
    ring
  have hconj (y : ℝ) : (starRingEnd ℂ) (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((-y : ℝ) : ℂ) * Complex.I) := by
    simpa [zpowSign] using zpowSign_gauge (-1) y 1
  unfold translationPhase
  rw [hconj, ← Complex.exp_add, ← Complex.exp_add, hk, inner_add_left, inner_sub_left]
  congr 1
  push_cast
  ring

/-- Spatial symmetry of the literal event implies spatial symmetry of its conditional data law. -/
theorem restricted_initialCoeff_map_translation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) (L : ℝ) (φ : Mom d → ℝ) {F : Set Ω}
    (hF : IsSymmetricEvent L φ g F) (x : Mom d) :
    (μ.restrict F).map (fun ω n => translationPhase L x n * initialCoeff L φ g ω n) =
      (μ.restrict F).map (initialCoeff L φ g) := by
  obtain ⟨A, hA, rfl, _, htrans⟩ := hF
  apply restricted_initialCoeff_map_phase hG L φ _ (norm_translationPhase L x) A hA (by
    simpa only [translationPhase, Complex.ofReal_neg] using htrans x)
  intro c hc
  change (fun n => (translationPhase L x n)⁻¹ * c n) ∈ A
  simp_rw [inv_translationPhase]
  simpa only [translationPhase, Complex.ofReal_neg] using htrans (-x) c hc

end WaveTurbulence.Induct
