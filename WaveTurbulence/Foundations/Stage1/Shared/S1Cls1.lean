/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF8
import Mathlib.Tactic

/-!
# Two canonical layered gardens decoded by the same data agree iff they agree at the native branch classes
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {S : Garden w}

theorem layered_eq_of_classes (D : ReconstructionData S) (hS : S.IsPlain) (W1 W2 : LayeredGarden w)
    (h1 : D.Decodes hS W1.garden) (h2 : D.Decodes hS W2.garden)
    (hc1 : W1.CanonCriterion p) (hc2 : W2.CanonCriterion p)
    (hcore : ∀ b, layerAt W1 (D.corePosition b) = layerAt W2 (D.corePosition b))
    (htree : ∀ b : GBranch S.tree, ∀ q ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).branching,
      layerAt W1 (addrExt (inflatedPosition S D.tree b.toNode) q) =
        layerAt W2 (addrExt (inflatedPosition S D.tree b.toNode) q))
    (hcouple : ∀ (qq : SourcePair S) (j : Fin 2) (r : Path),
      r ∈ (coupleForest (D.couple qq) j).branching →
      layerAt W1 (addrExt (coupleRoot D hS qq j) r) = layerAt W2 (addrExt (coupleRoot D hS qq j) r)) :
    W1 = W2 := by
  have hg1 : W1.garden = D.garden hS := rawOfGarden_injective_plain h1.1 (D.garden_plain hS)
    (h1.2.symm.trans (D.garden_raw hS).symm)
  have hg2 : W2.garden = D.garden hS := rawOfGarden_injective_plain h2.1 (D.garden_plain hS)
    (h2.2.symm.trans (D.garden_raw hS).symm)
  have hg : W1.garden = W2.garden := hg1.trans hg2.symm
  have hplain : W2.garden.IsPlain := h2.1
  have hC : W1.layer = extendBranchLayers W1.garden (fun c => W1.layer c.toNode) p :=
    (extendBranchLayers_eq_canonical W1 p hc1 h1.1).symm
  refine layered_eq_of_branches p hg hc2 hplain hC ?_
  intro c
  have e1 := layerAt_node W1 c.toNode
  have e2 := layerAt_node W2 (GBranch.toNode (tree := W2.garden.tree) ⟨c.1, hg ▸ c.2⟩)
  rw [← e1, ← e2]
  change layerAt W1 c.1 = layerAt W2 c.1
  have hmem : c.1.2 ∈ ((D.forest hS) c.1.1).branching := by
    exact (congrArg (fun G : Garden w => c.1.2 ∈ (G.tree c.1.1).branching) hg1).mp c.2
  obtain ⟨x, hx⟩ := (sourceBranchEquiv D hS).surjective (⟨c.1, hmem⟩ : GBranch (D.forest hS))
  have hxc : (sourceBranchEquiv D hS x).1 = c.1 := congrArg Subtype.val hx
  rw [← hxc]
  rcases x with b | (⟨qq, cc⟩ | ⟨b, q⟩)
  · exact hcore b
  · have : (coupleContextBranch D hS qq cc).1 = addrExt (coupleRoot D hS qq cc.1.1) cc.1.2 := by
      rcases cc with ⟨⟨j, r⟩, hc'⟩
      fin_cases j <;> rfl
    change layerAt W1 (coupleContextBranch D hS qq cc).1 = layerAt W2 (coupleContextBranch D hS qq cc).1
    rw [this]
    exact hcouple qq cc.1.1 cc.1.2 cc.2
  · exact htree b q.1 q.2

end WaveTurbulence.Stage1
