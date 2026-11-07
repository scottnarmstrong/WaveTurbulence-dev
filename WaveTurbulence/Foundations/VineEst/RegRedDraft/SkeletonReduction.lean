/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelNativeReduction

/-! # TARGET regred: reduction of the actual garden kernel to its skeleton -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

/-- Exactly the two native starred-kernel products in TARGET (redkg). The
canonical positive leaf selects each actual couple once; original roots use top. -/
noncomputable def reducedStarProduct {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (∏ p : SourcePair S, KQstar L γ δ F (nativeCoupleLayered D hS layer hLayer p)
    (parentClock top τ (p.firstLeaf hS).toNode) (parentClock top τ (p.secondLeaf hS).toNode)
    (cosetDecoration S L k₀ κ (p.firstLeaf hS).toNode)) *
  (∏ b : GBranch S.tree, KTstar L γ δ F (nativeChainLayered D hS layer hLayer b)
    (parentClock top τ b.toNode) (τ b) (cosetDecoration S L k₀ κ b.toNode))

theorem indicator_mul_right_apply {α : Type*} (A : Set α) (f g : α → ℂ) (x : α) :
    A.indicator f x * g x = A.indicator (fun y => f y*g y) x := by
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx,zero_mul]

theorem integral_coreKernelIntegrand_star {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    (∫ τ, coreKernelIntegrand D hS L γ δ layer top k₀ κ τ *
      ∏ s : ReplacementSlot S, nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ s) =
      (epsDec S κ : ℂ) * ∫ τ,
        (coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ) τ *
            reducedStarProduct D hS L γ δ F layer hLayer top k₀ κ τ) τ := by
  let A := coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top
  let P := phaseProd L γ δ S (cosetDecoration S L k₀ κ)
  let V := reducedStarProduct D hS L γ δ F layer hLayer top k₀ κ
  apply Eq.trans (b := ∫ τ, (epsDec S κ : ℂ) * A.indicator (fun τ => P τ*V τ) τ)
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro τ
    have hv : (∏ s : ReplacementSlot S, nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ s) = V τ :=
      nativeKernelValue_prod_star D hS L γ δ F layer hLayer top k₀ κ τ
    exact (mul_assoc (epsDec S κ : ℂ) (A.indicator P τ) _).trans
      (congrArg (fun z => (epsDec S κ : ℂ) * z)
        ((congrArg (fun z => A.indicator P τ * z) hv).trans (indicator_mul_right_apply A P V τ)))
  · exact integral_const_mul _ _

/-- TARGET regred L1724–1730, (redkg), in an arbitrary fixed lattice coset.
The right side uses the actual inherited KQstar and KTstar kernels. The only
analytic hypothesis is source input lattice absolute summability. -/
theorem kernelK_skeleton_reduction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    kernelK L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ n nfl =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              reducedStarProduct D hS L γ δ F layer hLayer top k₀ κ.1 τ) τ := by
  apply (kernelK_native_reduction D hS L γ δ F layer hLayer top k₀ n nfl hF).trans
  apply congrArg (fun z => ((coupling d L γ δ : ℂ)^S.order * S.zeta) * z)
  exact tsum_congr (fun κ => integral_coreKernelIntegrand_star D hS L γ δ F layer hLayer top k₀ κ.1)

/-- TARGET (redkg) for the actual ordinary garden KG, with top = p+1 in the
paper. The skeleton is pre-layered and retains its original parent clocks. -/
theorem KG_skeleton_reduction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (latticePoint L n)|) :
    KG L γ δ F (layeredReconstruction D hS layer hLayer) top n =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n 0, (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L 0 κ.1) τ *
              reducedStarProduct D hS L γ δ F layer hLayer top 0 κ.1 τ) τ := by
  apply kernelK_skeleton_reduction D hS L γ δ F layer hLayer top 0 n 0
  intro ℓ hℓ
  simpa only [zero_add] using hF ℓ hℓ

end WaveTurbulence.RegRed
