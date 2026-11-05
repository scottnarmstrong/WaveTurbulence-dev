/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBranches
/-! The actual branching-coordinate equivalence for factorizing grafted time domains. -/
@[expose] public section
namespace WaveTurbulence.Induct
open TTree

theorem leaf_eq_of_prefix_node (T : TTree) {a q : TTree.Path} (ha : a ∈ T.leaves)
    (hq : q ∈ T.nodes) (h : a <+: q) : a = q := by
  obtain ⟨r, rfl⟩ := h
  cases r with
  | nil => simp
  | cons i r =>
    exfalso
    have hc : a ++ [i] ∈ T.nodes := TTree.mem_nodes_of_prefix T hq ⟨r, by simp⟩
    exact TTree.not_mem_branching_of_mem_leaves T ha (TTree.branching_of_append_mem T hc)

abbrev AttachedBranch (T : TTree) (f : TTree.Path → TTree) :=
  Σ a : ↥T.leaves, ↥(f a.1).branching

def graftBranchMap (T : TTree) (f : TTree.Path → TTree) :
    ↥T.branching ⊕ AttachedBranch T f → ↥(graftTree T f).branching
  | .inl u => ⟨u.1, (mem_branching_graftTree T f _).mpr (Or.inl u.2)⟩
  | .inr x => ⟨x.1.1 ++ x.2.1,
      (mem_branching_graftTree T f _).mpr (Or.inr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩)⟩

/-- Branching coordinates are a disjoint sum of the top coordinates and all lower coordinates. -/
noncomputable def graftBranchEquiv (T : TTree) (f : TTree.Path → TTree) :
    ↥T.branching ⊕ AttachedBranch T f ≃ ↥(graftTree T f).branching :=
  Equiv.ofBijective (graftBranchMap T f) (by
    have hdisj (u : ↥T.branching) (x : AttachedBranch T f) : u.1 ≠ x.1.1 ++ x.2.1 := by
      intro he
      have hp : x.1.1 <+: u.1 := he ▸ List.prefix_append _ _
      have heq := leaf_eq_of_prefix_node T x.1.2 (TTree.branching_subset_nodes T u.2) hp
      apply TTree.not_mem_branching_of_mem_leaves T x.1.2
      rw [heq]
      exact u.2
    constructor
    · intro x y h
      cases x with
      | inl u =>
        cases y with
        | inl v =>
          have he : u.1 = v.1 := congrArg (fun z : ↥(graftTree T f).branching => z.1) h
          exact congrArg Sum.inl (Subtype.ext he)
        | inr v => exact False.elim (hdisj u v (congrArg (fun z : ↥(graftTree T f).branching => z.1) h))
      | inr u =>
        cases y with
        | inl v => exact False.elim (hdisj v u (congrArg (fun z : ↥(graftTree T f).branching => z.1) h.symm))
        | inr v =>
          obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
          obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := v
          have he : a ++ b = a' ++ b' := congrArg (fun z : ↥(graftTree T f).branching => z.1) h
          have hp : a' <+: a ++ b := he ▸ List.prefix_append _ _
          have haa : a = a' := by
            rcases List.prefix_or_prefix_of_prefix (List.prefix_append a b) hp with h | h
            · exact leaf_eq_of_prefix T ha ha' h
            · exact (leaf_eq_of_prefix T ha' ha h).symm
          subst a'
          have hbb : b = b' := List.append_cancel_left he
          subst b'
          rfl
    · rintro ⟨q, hq⟩
      rcases (mem_branching_graftTree T f q).mp hq with h | ⟨a, ha, b, hb, hab⟩
      · exact ⟨.inl ⟨q, h⟩, rfl⟩
      · exact ⟨.inr ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext hab⟩)

end WaveTurbulence.Induct
