/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayeredGraft
/-! Descendants stay inside the same attached root tree, with their lower addresses preserved. -/
public section
namespace WaveTurbulence.Induct
open TTree

theorem graft_attached_isDesc_iff {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (x y : ForestAttachedNode top f) :
    (graftForestNodeEquiv top f (.inr x)).IsDesc (graftForestNodeEquiv top f (.inr y)) ↔
      x.1 = y.1 ∧ x.2.1 <+: y.2.1 := by
  have hx := graftForestNodeEquiv_lower top f x
  have hy := graftForestNodeEquiv_lower top f y
  unfold GNode.IsDesc
  rw [hx, hy]
  constructor
  · rintro ⟨hj, hp⟩
    have hxp : x.1.1.2 <+: y.1.1.2 ++ y.2.1 := (List.prefix_append _ _).trans hp
    have hyp : y.1.1.2 <+: y.1.1.2 ++ y.2.1 := List.prefix_append _ _
    have he : x.1 = y.1 := by
      rcases List.prefix_or_prefix_of_prefix hxp hyp with h | h
      · exact GLeaf.eq_of_isDesc ⟨hj, h⟩
      · exact (GLeaf.eq_of_isDesc ⟨hj.symm, h⟩).symm
    refine ⟨he, ?_⟩
    obtain ⟨r, hr⟩ := hp
    have hpath := congrArg (fun a : GLeaf top => a.1.2) he
    have hcancel : x.1.1.2 ++ (x.2.1 ++ r) = x.1.1.2 ++ y.2.1 := by
      simpa only [List.append_assoc, hpath] using hr
    exact ⟨r, List.append_cancel_left hcancel⟩
  · rintro ⟨he, hp⟩
    refine ⟨congrArg (fun a : GLeaf top => a.1.1) he, ?_⟩
    obtain ⟨r, hr⟩ := hp
    refine ⟨r, ?_⟩
    have hpath := congrArg (fun a : GLeaf top => a.1.2) he
    rw [List.append_assoc, hr, hpath]

end WaveTurbulence.Induct
