/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftParents
public import WaveTurbulence.Foundations.XChain.LayeredGraftBounds
public import WaveTurbulence.Foundations.XChain.GraftPairedBlock
public import WaveTurbulence.Foundations.XChain.GardenRootPairing
/-! The canonicality inequality inside each proper lower component of a graft. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem graft_lower_criterion {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) (B : P.parts)
    (hcanon : IsCanonG p (low B)) (a b : GNode (low B).garden.tree)
    (hinc : (lowerNodeEmbedding top P (fun B => (low B).garden) B a).Incomparable
      (lowerNodeEmbedding top P (fun B => (low B).garden) B b))
    (hcp : (gardenGraft sig top P (fun B => (low B).garden) hplain hsig).CompletelyPaired
      ((lowerNodeEmbedding top P (fun B => (low B).garden) B a).leavesBelow ∪
       (lowerNodeEmbedding top P (fun B => (low B).garden) B b).leavesBelow)) :
    min ((layeredGardenGraft sig top P low p hplain hsig hbound).parentLayer p
          (lowerNodeEmbedding top P (fun B => (low B).garden) B a))
        ((layeredGardenGraft sig top P low p hplain hsig hbound).parentLayer p
          (lowerNodeEmbedding top P (fun B => (low B).garden) B b)) ≤
      max ((low B).layer a) ((low B).layer b) := by
  cases p with
  | zero => exact False.elim hcanon
  | succ q =>
    obtain ⟨hw, _, hirr, hcrit⟩ := hcanon
    have hic : a.Incomparable b := by
      constructor
      · intro h
        exact hinc.1 ((garden_lower_isDesc_iff top P (fun B => (low B).garden) B a b).mpr h)
      · intro h
        exact hinc.2 ((garden_lower_isDesc_iff top P (fun B => (low B).garden) B b a).mpr h)
    have hcp' := (lower_subtrees_completelyPaired_iff sig top P
      (fun B => (low B).garden) hplain hsig B a b).mp hcp
    have hc := hcrit.2 a b hic hcp'
    by_cases ha : a.1.2 = []
    · by_cases hb : b.1.2 = []
      · have hea : a = GNode.root (low B).garden.tree a.1.1 :=
          Subtype.ext (Prod.ext rfl ha)
        have heb : b = GNode.root (low B).garden.tree b.1.1 :=
          Subtype.ext (Prod.ext rfl hb)
        have he := congrArg₂ (fun x y : GNode (low B).garden.tree =>
          x.leavesBelow ∪ y.leavesBelow) hea heb
        have hp := (congrArg (low B).garden.CompletelyPaired he).mp hcp'
        exact False.elim (not_paired_root_pair (low B).garden hw hirr a.1.1 b.1.1 hp)
      · have hpb := parentLayer_le_of_layer_le (low B) q hcrit.1 b
        have hpa : (low B).parentLayer q a = q := by
          simp only [LayeredGarden.parentLayer, ha, ite_true]
        rw [hpa, min_eq_right hpb] at hc
        exact (min_le_right _ _).trans
          ((graft_parentLayer_internal sig top P low (q + 1) hplain hsig hbound B b hb q).le.trans hc)
    · by_cases hb : b.1.2 = []
      · have hpa := parentLayer_le_of_layer_le (low B) q hcrit.1 a
        have hpb : (low B).parentLayer q b = q := by
          simp only [LayeredGarden.parentLayer, hb, ite_true]
        rw [hpb, min_eq_left hpa] at hc
        exact (min_le_left _ _).trans
          ((graft_parentLayer_internal sig top P low (q + 1) hplain hsig hbound B a ha q).le.trans hc)
      · have hea := graft_parentLayer_internal sig top P low (q + 1) hplain hsig hbound B a ha q
        have heb := graft_parentLayer_internal sig top P low (q + 1) hplain hsig hbound B b hb q
        exact (congrArg₂ min hea heb).le.trans hc

end WaveTurbulence.Induct
