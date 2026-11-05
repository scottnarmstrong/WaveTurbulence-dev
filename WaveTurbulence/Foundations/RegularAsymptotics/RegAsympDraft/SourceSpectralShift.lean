/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceFrequencyRows
public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization

/-! # Actual regular-couple spectral shifts and their frequency bound -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh WithLp

/-- The actual root shift is the sum of independent leaf frequencies. -/
theorem actual_spectralShift_root {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ) :
    (coupleMomentumData hQ hG).spectralShift ξ none = ∑ a, toLp 2 (ξ (.inl a)) := by
  simp [MomentumTreeData.spectralShift,Fintype.sum_sum_type,MomentumTreeData.profileRow,
    coupleMomentumData,sourceNodeRow_root_column,momentumUnitRow]


/-- Every actual link shift is its leaf pullback plus the independent link frequency. -/
theorem actual_spectralShift_link {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ)
    (p : Fin Q.links.length × Fin 2) :
    (coupleMomentumData hQ hG).spectralShift ξ (some p) =
      sourceFrequencyPullback hQ hG (fun a => toLp 2 (ξ (.inl a))) (some p) + toLp 2 (ξ (.inr p)) := by
  classical
  simp [MomentumTreeData.spectralShift,Fintype.sum_sum_type,MomentumTreeData.profileRow,
    coupleMomentumData,momentumUnitRow,sourceFrequencyPullback,Int.cast_smul_eq_zsmul ℝ]


/-- The pointwise full-spectrum moment controls each actual link shift,
with only a linear source-order factor. -/
theorem norm_actual_spectralShift_link_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (ξ : LocalizedCellIndex Q.links.length (2*Q.links.length+1) → Fin d → ℝ)
    (p : Fin Q.links.length × Fin 2) :
    ‖(coupleMomentumData hQ hG).spectralShift ξ (some p)‖ ≤
      (1+(Q.size:ℝ)) * (∑ i, ‖toLp 2 (ξ i)‖) := by
  rw [actual_spectralShift_link hQ hG ξ p]
  have hp : ‖toLp 2 (ξ (.inr p))‖ ≤ ∑ q : Fin Q.links.length × Fin 2, ‖toLp 2 (ξ (.inr q))‖ :=
    Finset.single_le_sum (f := fun q : Fin Q.links.length × Fin 2 => ‖toLp 2 (ξ (.inr q))‖)
      (fun q _ => norm_nonneg _) (Finset.mem_univ p)
  have hq : 0 ≤ (Q.size:ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ∑ q : Fin Q.links.length × Fin 2, ‖toLp 2 (ξ (.inr q))‖ :=
    Finset.sum_nonneg (fun q _ => norm_nonneg _)
  have hh := (norm_add_le _ _).trans (add_le_add
    (norm_sourceFrequencyPullback_le hQ hG (fun a => toLp 2 (ξ (.inl a))) (some p)) hp)
  rw [Fintype.sum_sum_type]
  nlinarith

end WaveTurbulence.RegAsymp
