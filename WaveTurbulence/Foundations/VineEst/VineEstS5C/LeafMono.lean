/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity

/-! # Large-constant monotonicity of the literal (R33, `XNormRestr 30d`) leafwise coherent gate

Copy-and-edit of lg-spine-u `leafwiseCoherentApproximation_largeConstantMonotone` (stated there for the order-zero
consequence `LeafwiseCoherentApproximationOrder0At`) for the literal body `LeafwiseCoherentApproximationAt`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.LGSpine Set

theorem leafwiseCoherentAt_largeConstantMonotone : LargeConstantMonotone LeafwiseCoherentApproximationAt := by
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

end WaveTurbulence.VineEstS5C
