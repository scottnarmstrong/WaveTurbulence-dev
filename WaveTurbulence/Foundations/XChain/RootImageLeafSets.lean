/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeavesBelowSetOperations
/-! Finite root-image leaf identities used for uniqueness of graft partitions. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem biUnion_map_congr {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (r : α ↪ β) (l : γ ↪ δ) (R : β → Finset δ) (S : α → Finset γ)
    (h : ∀ a, R (r a) = (S a).map l) (K : Finset α) :
    (K.map r).biUnion R = (K.biUnion S).map l := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    have hm : x ∈ (S a).map l := (congrArg (fun T => x ∈ T) (h a)).mp hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hm
    exact Finset.mem_map.mpr ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩, hbx⟩
  · intro hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hx
    obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
    have hm : x ∈ (S a).map l := Finset.mem_map.mpr ⟨b, hba, hbx⟩
    exact Finset.mem_biUnion.mpr ⟨r a, Finset.mem_map.mpr ⟨a, ha, rfl⟩,
      (congrArg (fun T => x ∈ T) (h a)).mpr hm⟩

theorem leavesOf_biUnion_roots {w : ℕ} (G : Garden w) (A : Finset (Fin w)) :
    G.leavesOf A = A.biUnion (fun j => (GNode.root G.tree j).leavesBelow) := by
  classical
  ext ℓ
  simp [Garden.leavesOf, GNode.leavesBelow, GNode.IsDesc, GNode.root, GLeaf.toNode]

end WaveTurbulence.Induct
