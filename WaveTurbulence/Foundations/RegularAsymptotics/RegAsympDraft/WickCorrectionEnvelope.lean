/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternEnvelopeMass
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceMeasurable

/-! # Actual admissible patterns of the source Wick correction -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset MeasureTheory WithLp ApproxNT

/-- Discard only source patterns proved identically zero on special energies. -/
theorem normalizedWickCorrection_eq_sum_admissible {d n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    normalizedWickCorrection L δ γ z β γ' J C lam =
      ∑ σ ∈ wickAdmissiblePatterns J, normalizedWickSlice L δ γ σ z β γ' J C lam := by
  classical
  rw [normalizedWickCorrection_eq_sum hL,wickAdmissiblePatterns,Finset.sum_filter]
  apply sum_congr rfl
  intro σ _
  by_cases h : Disjoint (wickTracedLinks σ) J
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact normalizedWickSlice_eq_zero_of_not_disjoint L δ γ σ z β γ' J C lam h

/-- The actual source correction has only the finite geometric family
of admissible slice norms, with no absolute value inside an NT sum. -/
theorem norm_normalizedWickCorrection_le_sum {d n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    ‖normalizedWickCorrection L δ γ z β γ' J C lam‖ ≤
      ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J}, ‖normalizedWickSlice L δ γ σ.val z β γ' J C lam‖ := by
  have he : normalizedWickCorrection L δ γ z β γ' J C lam =
      ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J}, normalizedWickSlice L δ γ σ.val z β γ' J C lam :=
    (normalizedWickCorrection_eq_sum_admissible hL δ γ z β γ' J C lam).trans
      (Finset.sum_subtype (wickAdmissiblePatterns J) (fun _ => Iff.rfl) _)
  rw [he]
  exact norm_sum_le _ _

/-- Joint source measurability retains the literal finite-family identity. -/
theorem stronglyMeasurable_normalizedWickCorrection_joint {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      normalizedWickCorrection L δ γ z p.2.1 p.2.2 J C p.1) := by
  classical
  simp_rw [normalizedWickCorrection_eq_sum hL]
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro σ _
  exact (stronglyMeasurable_normalizedWickSlice_joint L δ γ σ z J hC).measurable

end WaveTurbulence.RegAsymp
