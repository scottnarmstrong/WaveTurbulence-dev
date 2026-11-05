/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBranchEquiv
/-! The node-coordinate equivalence needed to transport decorations and layerings. -/
@[expose] public section
namespace WaveTurbulence.Induct
open TTree

theorem mem_nodes_graftTree (T : TTree) (f : TTree.Path → TTree) (q : TTree.Path) :
    q ∈ (graftTree T f).nodes ↔ q ∈ T.branching ∨
      ∃ a ∈ T.leaves, ∃ b ∈ (f a).nodes, a ++ b = q := by
  constructor
  · intro hq
    rcases (TTree.mem_nodes_iff _ _).mp hq with hl | hb
    · obtain ⟨a, ha, b, hb, he⟩ := (mem_leaves_graftTree T f q).mp hl
      exact Or.inr ⟨a, ha, b, TTree.leaves_subset_nodes _ hb, he⟩
    · rcases (mem_branching_graftTree T f q).mp hb with hb | ⟨a, ha, b, hb, he⟩
      · exact Or.inl hb
      · exact Or.inr ⟨a, ha, b, TTree.branching_subset_nodes _ hb, he⟩
  · rintro (hb | ⟨a, ha, b, hb, rfl⟩)
    · exact TTree.branching_subset_nodes _ ((mem_branching_graftTree T f q).mpr (Or.inl hb))
    · rcases (TTree.mem_nodes_iff _ _).mp hb with hl | hb
      · exact TTree.leaves_subset_nodes _ ((mem_leaves_graftTree T f _).mpr ⟨a, ha, b, hl, rfl⟩)
      · exact TTree.branching_subset_nodes _ ((mem_branching_graftTree T f _).mpr
          (Or.inr ⟨a, ha, b, hb, rfl⟩))

abbrev AttachedNode (T : TTree) (f : TTree.Path → TTree) :=
  Σ a : ↥T.leaves, ↥(f a.1).nodes

def graftNodeMap (T : TTree) (f : TTree.Path → TTree) :
    ↥T.branching ⊕ AttachedNode T f → ↥(graftTree T f).nodes
  | .inl u => ⟨u.1, (mem_nodes_graftTree T f _).mpr (Or.inl u.2)⟩
  | .inr x => ⟨x.1.1 ++ x.2.1,
      (mem_nodes_graftTree T f _).mpr (Or.inr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩)⟩

/-- Node coordinates are a disjoint sum of top branching nodes and all lower nodes. -/
noncomputable def graftNodeEquiv (T : TTree) (f : TTree.Path → TTree) :
    ↥T.branching ⊕ AttachedNode T f ≃ ↥(graftTree T f).nodes :=
  Equiv.ofBijective (graftNodeMap T f) (by
    have hdisj (u : ↥T.branching) (x : AttachedNode T f) : u.1 ≠ x.1.1 ++ x.2.1 := by
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
          have he : u.1 = v.1 := congrArg (fun z : ↥(graftTree T f).nodes => z.1) h
          exact congrArg Sum.inl (Subtype.ext he)
        | inr v => exact False.elim (hdisj u v (congrArg (fun z : ↥(graftTree T f).nodes => z.1) h))
      | inr u =>
        cases y with
        | inl v => exact False.elim (hdisj v u (congrArg (fun z : ↥(graftTree T f).nodes => z.1) h.symm))
        | inr v =>
          obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
          obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := v
          have he : a ++ b = a' ++ b' := congrArg (fun z : ↥(graftTree T f).nodes => z.1) h
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
      rcases (mem_nodes_graftTree T f q).mp hq with h | ⟨a, ha, b, hb, hab⟩
      · exact ⟨.inl ⟨q, h⟩, rfl⟩
      · exact ⟨.inr ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext hab⟩)

end WaveTurbulence.Induct
