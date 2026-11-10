/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.Leaves

/-! # Leafwise skeleton reduction of the garden kernel (REGRED-LEAF, RULINGS R24 D4)

TARGET regred (L1724–1730), (redkg), for the leaf-modified kernel `kernelLeaves` of TARGET L2065–2067
(RULINGS R9(a)): the same factorization as `RegRed.KG_skeleton_reduction`, with the regular parts' native
kernels leaf-modified (`coupleLeaves`, `treeLeaves` with the pulled-back leaf profiles).  The only analytic
hypothesis is the source absolute lattice summability of the profiles at the input leaves of the full
garden.  The version `kernelLeaves_skeleton_reduction_sel` restricts the decoration sum by a predicate on
skeleton decorations (TARGET L1950). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.LGSpine

theorem integral_coreKernelIntegrand_starLeaves {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    (∫ τ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ τ *
      ∏ s : ReplacementSlot S, nativeKernelValueN D hS L γ δ (fun a => H a.1) layer hLayer tt k₀ κ τ s) =
      (epsDec S κ : ℂ) * ∫ τ,
        (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ) τ *
            reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ τ) τ := by
  let Ad := coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  let P := phaseProd L γ δ S (cosetDecoration S L k₀ κ)
  let V := reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ
  apply Eq.trans (b := ∫ τ, (epsDec S κ : ℂ) * Ad.indicator (fun τ => P τ * V τ) τ)
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro τ
    have hv : (∏ s : ReplacementSlot S,
        nativeKernelValueN D hS L γ δ (fun a => H a.1) layer hLayer tt k₀ κ τ s) = V τ :=
      prod_nativeKernelValueN_leaves D hS L γ δ H layer hLayer tt k₀ κ τ
    exact (mul_assoc (epsDec S κ : ℂ) (Ad.indicator P τ) _).trans
      (congrArg (fun z => (epsDec S κ : ℂ) * z)
        ((congrArg (fun z => Ad.indicator P τ * z) hv).trans (indicator_mul_right_apply Ad P V τ)))
  · exact integral_const_mul _ _

open scoped Classical in
/-- The decoration-restricted leaf kernel is the sum of the restricted skeleton decorations. -/
theorem kernelLeavesSel_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (hG : ∀ b, ¬ LG.garden.IsFlowerParent b) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) :
    kernelLeavesSel L γ δ LG H up s k₀ nroot nfl sel =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          ∫ τ, kernelAllIntegrandN L γ δ LG (fun a => H a.1) up s k₀ κ τ else 0 := by
  classical
  unfold kernelLeavesSel
  congr 1
  apply tsum_congr
  intro κ
  by_cases h : sel κ
  · simp only [h, ite_true]
    exact ((integral_kernelAllIntegrandN L γ δ LG (fun a => H a.1) hG up s k₀ κ).trans
      (integral_kernelIntegrandN L γ δ LG (fun a => H a.1) up s k₀ κ)).symm
  · simp only [h, ite_false]

open scoped Classical in
/-- TARGET (redkg), leafwise, with a restriction `selSk` of the skeleton decoration (L1950), in an
arbitrary fixed lattice coset `k₀`. -/
theorem kernelLeaves_skeleton_reduction_sel {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀+latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    kernelLeavesSel L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ.1 τ) τ else 0 := by
  rw [kernelLeavesSel_eq_integral L γ δ (layeredReconstruction D hS layer hLayer) H _ _ k₀
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) n nfl]
  refine (kernelNode_native_reduction_sel D hS L γ δ (fun a => H a.1) layer hLayer tt k₀ n nfl hH
    selSk).trans ?_
  apply congrArg (fun z => ((coupling d L γ δ : ℂ)^S.order * S.zeta) * z)
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    exact integral_coreKernelIntegrand_starLeaves D hS L γ δ H layer hLayer tt k₀ κ.1
  · simp only [hκ, ite_false]

end WaveTurbulence.RegRedLeaf
