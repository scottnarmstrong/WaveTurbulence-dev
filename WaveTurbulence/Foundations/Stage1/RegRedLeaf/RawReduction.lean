/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.ReducedDecomp
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelNativeReduction

/-! # Skeleton reduction of the node-profile kernel, with a skeleton-level decoration restriction

REGRED `KernelRawReduction` for a node profile `A` (REGRED-LEAF, RULINGS R24 D4).  The decoration sum of
the reconstructed garden is split along `decorationFiberEquiv` into a skeleton decoration and independent
native fibres.  The new ingredient is a restriction `selSk` of the *skeleton* decoration (TARGET L1950, the
SG/LG/ZG indicator `Z`): the full-decoration restriction is its pullback along `collapseGenDecoration`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed

open scoped Classical in
/-- The restricted decoration sum splits along the skeleton/native fibre equivalence. -/
theorem tsum_integral_sel_reduction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀+latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    (∑' κ : GenDecoration (D.garden hS) d n nfl,
      if selSk (collapseGenDecoration D hS κ) then
        ∫ τ, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ
      else 0) =
      ∑' κ : GenDecoration S d n nfl, if selSk κ then
        ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ.1 τ *
          ∏ s : ReplacementSlot S, ∑' ρ : NativeRelativeDecoration D hS d s,
            ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ.1 τ s ρ t
      else 0 := by
  classical
  let f : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    ∫ τ, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ
  have hs : Summable f := summable_integral_kernelAllIntegrandN L γ δ
    (layeredReconstruction D hS layer hLayer) A
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ n nfl
    (lone_count_le_one_of_plain _ (D.garden_plain hS)) hA
  let g : GenDecoration (D.garden hS) d n nfl → ℂ := fun κ =>
    if selSk (collapseGenDecoration D hS κ) then f κ else 0
  have hgs : Summable g := by
    apply Summable.of_norm_bounded hs.norm
    intro κ
    by_cases h : selSk (collapseGenDecoration D hS κ)
    · simp only [g, h, ite_true, le_refl]
    · simp only [g, h, ite_false, norm_zero, norm_nonneg]
  have hp : Summable (fun p : GenDecoration S d n nfl ×
      ((s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) =>
        g (glueGenDecoration D hS p.1 p.2)) :=
    hgs.comp_injective (decorationFiberEquiv D hS n nfl).symm.injective
  have hsplit : (∑' κ, g κ) = ∑' κ : GenDecoration S d n nfl,
      ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) :=
    (tsum_decorationFiberEquiv D hS n nfl g).trans hp.tsum_prod
  change (∑' κ, g κ) = _
  rw [hsplit]
  apply tsum_congr
  intro κ
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = f (glueGenDecoration D hS κ ρ) := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_true]
    rw [tsum_congr hg]
    apply Eq.trans (b := ∑' ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
      ∫ τ, reducedDecorationIntegrandN D hS L γ δ A layer hLayer tt k₀ (glueGenDecoration D hS κ ρ) τ)
    · exact tsum_congr (fun ρ => integral_kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer
        tt k₀ (glueGenDecoration D hS κ ρ))
    · apply (tsum_integral_reduced_fixed_skeletonN D hS L γ δ A layer hLayer tt k₀ κ hA).trans
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun τ => tsum_reduced_fixed_skeletonN D hS L γ δ A layer hLayer tt k₀ κ τ hA))
  · simp only [hκ, ite_false]
    have hg : ∀ ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s,
        g (glueGenDecoration D hS κ ρ) = 0 := by
      intro ρ
      simp only [g, collapseGenDecoration_glue, hκ, ite_false]
    rw [tsum_congr hg, tsum_zero]

end WaveTurbulence.RegRedLeaf
