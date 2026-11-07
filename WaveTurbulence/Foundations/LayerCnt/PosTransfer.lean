/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.RegionErase2
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationGeometry
public import WaveTurbulence.Foundations.Molecule.LFTwist.ExpandedPlacement
public import WaveTurbulence.Foundations.Molecule.TwistParents
import Mathlib.Tactic

/-! # Skeleton nodes inside a decoded garden: parents, layers, incomparability

For a decoding `E` of the skeleton `S` in `LH.garden`, the node `E.decodedNode a` sits at the inflated position of `a`.
Its parent is the retained core branch of the parent of `a`, so its parent layer is the skeleton's `branchParentValue`
of the induced pre-layering; nodes with nil tree (branches) or trivial couple (leaves) carry the expected layers.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree Reg Reg.Skeleton Links LFTwist Twist
variable {w : ℕ} {S G : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)

include hS in
theorem decodedNode_parent (a : GNode S.tree) (ha : a.1.2 ≠ []) (hn : (D.decodedNode hS hd a).1.2 ≠ []) :
    GNode.parent (D.decodedNode hS hd a) hn = D.decodedCoreBranch hS hd (GNode.parent a ha) := by
  apply parent_eq_of_child hn (i := a.1.2.getLast ha)
  apply Subtype.ext
  exact (congrArg (fun z : GNode S.tree => inflatedPosition S D.tree z) (child_parent a ha).symm).trans
    (D.core_child_position _ _)

theorem parentLayer_decodedNode (LH : LayeredGarden w) (E : ReconstructionData S)
    (he : E.Decodes hS LH.garden) (p : ℕ) (a : GNode S.tree) :
    LH.parentLayer p (E.decodedNode hS he a) =
      branchParentValue S (inducedPrelayer LH E hS he) p a := by
  by_cases ha : a.1.2 = []
  · have h1 : (E.decodedNode hS he a).1.2 = [] := by
      change (inflatedPosition S E.tree a).2 = []
      rw [inflatedPosition]
      simp [ha]
    simp only [LayeredGarden.parentLayer, branchParentValue, h1, ha, dite_true, ite_true]
  · have hn : (E.decodedNode hS he a).1.2 ≠ [] := inflatedPosition_nonroot S E.tree a ha
    rw [branchParentValue, dite_eq_right ha, parentLayer_nonroot LH p _ hn, decodedNode_parent E hS he a ha hn]
    rfl

theorem decodedNode_branch_nil (E : ReconstructionData S) (he : E.Decodes hS G) (b : GBranch S.tree)
    (hb : E.tree b = .nil) : E.decodedNode hS he b.toNode = (E.decodedCoreBranch hS he b).toNode := by
  apply Subtype.ext
  change inflatedPosition S E.tree b.toNode = E.corePosition b
  rw [ReconstructionData.corePosition, hb, RegChain.lonePath, addrExt_nil]

theorem decodedNode_incomp (E : ReconstructionData S) (he : E.Decodes hS G) (a a' : GNode S.tree)
    (h : a.Incomparable a') : (E.decodedNode hS he a).Incomparable (E.decodedNode hS he a') := by
  have h0 : IncompAddr a.1 a'.1 := ⟨fun hb => h.1 ⟨hb.1.symm, hb.2⟩, fun hb => h.2 ⟨hb.1.symm, hb.2⟩⟩
  have h2 := inflatedPosition_incomp S E.tree a a' h0
  exact ⟨fun hb => h2.1 ⟨hb.1.symm, hb.2⟩, fun hb => h2.2 ⟨hb.1.symm, hb.2⟩⟩

/-- Inflated positions reflect the ancestor relation. -/
theorem below_of_pos_below (X : GBranch S.tree → RegChain) (u v : GNode S.tree)
    (h : Below (inflatedPosition S X u) (inflatedPosition S X v)) : Below u.1 v.1 := by
  by_cases huv : Below u.1 v.1
  · exact huv
  · by_cases hvu : Below v.1 u.1
    · have h2 := inflatedPosition_below S X v u hvu
      have he : inflatedPosition S X u = inflatedPosition S X v :=
        Prod.ext h.1.symm (List.IsPrefix.eq_of_length (h.2) (Nat.le_antisymm h.2.length_le h2.2.length_le))
      have := inflatedPosition_injective S X he
      subst this
      exact huv ⟨rfl, List.prefix_refl _⟩ |>.elim
    · exact ((inflatedPosition_incomp S X u v ⟨huv, hvu⟩).1 h).elim

end WaveTurbulence.LayerCnt
