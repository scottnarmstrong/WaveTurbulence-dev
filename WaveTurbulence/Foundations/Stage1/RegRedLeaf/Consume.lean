/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.SkeletonLeaves
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise

/-! # The leafwise skeleton reduction in the shape consumed by `Stage1Piece.Represents` (REGRED-LEAF)

`Represents` (C1) is `val = ∑ LG ∈ members, F.valueSel tt base roots LG (sel LG)`.  For a member garden
`LG = layeredReconstruction D hS layer hLayer` and a decoration restriction pulled back from the skeleton,
`LeafFamily.valueSel_skeleton_reduction` rewrites `F.valueSel` as the signed sum, over the family, of the
skeleton expression (redkg) with the leafwise native kernels.  The summability hypothesis is discharged
from leafwise control (`LeafwiseControlled.summable_coset`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.LGSpine

open scoped Classical in
/-- `kernelLeaves_skeleton_reduction_sel` with the summability premise discharged by leafwise control. -/
theorem kernelLeaves_skeleton_reduction_sel_of_controlled {w d : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (B : (Fin w × TTree.Path) → NNReal)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B)
    (hd : 1 ≤ d) (hL : 1 ≤ L)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (selSk : GenDecoration S d n nfl → Prop) :
    kernelLeavesSel L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ.1 τ) τ else 0 :=
  kernelLeaves_skeleton_reduction_sel D hS L γ δ H layer hLayer tt k₀ n nfl
    (hctrl.summable_coset hd hL k₀) selSk

open scoped Classical in
/-- `Stage1Piece.Represents` (C1) for a member garden that is a reconstruction of a skeleton: the family
value with the decoration restriction pulled back from the skeleton is the signed sum of the skeleton
expressions with leafwise native kernels. -/
theorem LeafFamily.valueSel_skeleton_reduction {P : WTParams} {R : ℕ} (F : LeafFamily P (2 * R))
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop) :
    F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) =
      @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℂ _
        (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer))) fun i =>
        ((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ) *
          ((coupling P.d P.L P.γ P.δ : ℂ)^S.order * S.zeta *
            ∑' κ : GenDecoration S P.d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
              (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
                (fun τ => phaseProd P.L P.γ P.δ S (cosetDecoration S P.L base κ.1) τ *
                  reducedStarProductLeaves D hS P.L P.γ P.δ
                    (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer tt base κ.1 τ) τ
            else 0) := by
  unfold LeafFamily.valueSel
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => ((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ) * z)
    (kernelLeaves_skeleton_reduction_sel_of_controlled D hS P.L P.γ P.δ
      (F.H (layeredReconstruction D hS layer hLayer) i) (F.B (layeredReconstruction D hS layer hLayer) i)
      layer hLayer (hctrl i) hd hL tt base roots 0 selSk)

end WaveTurbulence.RegRedLeaf
