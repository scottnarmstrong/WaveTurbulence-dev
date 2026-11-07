/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
import Mathlib.Tactic

/-!
# S2 REPRESENTS: large-constant monotonicity of the literal (30d) leafwise coherent gate

lg-spine-u (AMEND3) proves `LargeConstantMonotone` only for `LeafwiseCoherentApproximationOrder0At`.  The proof for
the 30d gate `LeafwiseCoherentApproximationAt` is the same (the error bound `regBound` and the separation
constants are monotone in `C₁`; the error norm is the same on both sides), copied here verbatim with the new norm.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine

theorem leafwiseCoherentApproximation30_largeConstantMonotone :
    LargeConstantMonotone LeafwiseCoherentApproximationAt := by
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

end WaveTurbulence.Represents
