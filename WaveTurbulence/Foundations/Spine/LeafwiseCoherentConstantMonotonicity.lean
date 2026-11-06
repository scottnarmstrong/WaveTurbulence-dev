/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLargeConstantBounds
/-! Large-constant monotonicity of the literal leafwise Prop 6.1 input. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem leafwiseSeparated_largeConstants_mono (P : WTParams) {C₁ C₂ : ℝ}
    (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁) (n W : ℕ) (T : Set (Fin 2 → ℝ))
    (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (cost : ℝ) (hcost : 0 ≤ cost)
    (h : LeafwiseSeparated P n W T f cost) :
    LeafwiseSeparated {P with C₁ := C₁, C₂ := C₂} n W T f cost := by
  obtain ⟨m, J, M, hm, heq, hJ, hM⟩ := h
  refine ⟨m, J, M, hm, heq, ?_, ?_⟩
  · intro i
    exact (hJ i).trans (ENNReal.ofReal_le_ofReal (source_factor_mono hC hCC n))
  · intro i
    exact (hM i).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (source_factor_mono hC hCC n) hcost))

theorem leafwiseCoherentApproximation_largeConstantMonotone :
    LargeConstantMonotone LeafwiseCoherentApproximationOrder0At := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  intro p hp n hn
  rw [N_largeConstants] at hn
  constructor
  · intro Q LG q q' hqq' hqp hsize hcoh H B hcontrol
    obtain ⟨he, hnon, hsep⟩ := (hsource p hp n hn).1 Q LG q q' hqq' hqp hsize hcoh H B hcontrol
    refine ⟨he.trans ?_, hnon, ?_⟩
    · exact mul_le_mul_of_nonneg_right (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n 1) (by positivity)
    · exact leafwiseSeparated_largeConstants_mono P hc0 hCC n (30 * P.d) _ _ _ (by
        unfold leafSizeProduct
        exact Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)) hsep
  · intro X LG q q' hqq' hqp hsize hcoh H B hcontrol
    obtain ⟨he, hnon, hsep⟩ := (hsource p hp n hn).2 X LG q q' hqq' hqp hsize hcoh H B hcontrol
    refine ⟨he.trans ?_, hnon, ?_⟩
    · exact mul_le_mul_of_nonneg_right (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n 1) (by positivity)
    · exact leafwiseSeparated_largeConstants_mono P hc0 hCC n 0 _ _ _ (by
        unfold leafSizeProduct
        exact Finset.prod_nonneg (fun _ _ => NNReal.coe_nonneg _)) hsep

end WaveTurbulence.LGSpine
