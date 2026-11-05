/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeGraft
/-! The leaf bijection underlying grafting, without identifying distinct ordered trees. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset TTree

theorem mem_leaves_graftTree (T : TTree) (f : TTree.Path → TTree) (q : TTree.Path) :
    q ∈ (graftTree T f).leaves ↔ ∃ a ∈ T.leaves, ∃ b ∈ (f a).leaves, a ++ b = q := by
  induction T generalizing f q with
  | leaf => simp [graftTree, TTree.leaves]
  | node l m r hl hm hr =>
    constructor
    · intro h
      simp only [graftTree, TTree.leaves, Finset.mem_union] at h
      rcases h with (h | h) | h
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        obtain ⟨a, ha, b, hb, rfl⟩ := (hl _ _).mp hu
        exact ⟨0 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        obtain ⟨a, ha, b, hb, rfl⟩ := (hm _ _).mp hu
        exact ⟨1 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        obtain ⟨a, ha, b, hb, rfl⟩ := (hr _ _).mp hu
        exact ⟨2 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [TTree.leaves, Finset.mem_union] at ha
      simp only [graftTree, TTree.leaves, Finset.mem_union]
      rcases ha with (ha | ha) | ha
      · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
        exact Or.inl (Or.inl (TTree.mem_pre.mpr ⟨a ++ b, (hl _ _).mpr ⟨a, hleaf, b, hb, rfl⟩, rfl⟩))
      · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
        exact Or.inl (Or.inr (TTree.mem_pre.mpr ⟨a ++ b, (hm _ _).mpr ⟨a, hleaf, b, hb, rfl⟩, rfl⟩))
      · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
        exact Or.inr (TTree.mem_pre.mpr ⟨a ++ b, (hr _ _).mpr ⟨a, hleaf, b, hb, rfl⟩, rfl⟩)

theorem leaf_eq_of_prefix (T : TTree) {a b : TTree.Path} (ha : a ∈ T.leaves)
    (hb : b ∈ T.leaves) (hab : a <+: b) : a = b := by
  let x : GLeaf (fun _ : Fin 1 => T) := ⟨(0, a), ha⟩
  let y : GLeaf (fun _ : Fin 1 => T) := ⟨(0, b), hb⟩
  have he : x = y := GLeaf.eq_of_isDesc ⟨rfl, hab⟩
  exact congrArg (fun z => z.1.2) he

/-- Every leaf of the grafted tree is uniquely a top leaf followed by a lower leaf. -/
noncomputable def graftLeafEquiv (T : TTree) (f : TTree.Path → TTree) :
    (Σ a : {a // a ∈ T.leaves}, {b // b ∈ (f a.1).leaves}) ≃
      {q // q ∈ (graftTree T f).leaves} :=
  Equiv.ofBijective (fun x => ⟨x.1.1 ++ x.2.1,
    (mem_leaves_graftTree T f _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩) (by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have he : a ++ b = a' ++ b' := congrArg Subtype.val h
      have h1 : a <+: a ++ b := List.prefix_append _ _
      have h2 : a' <+: a ++ b := he ▸ List.prefix_append _ _
      have haa : a = a' := by
        rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
        · exact leaf_eq_of_prefix T ha ha' h
        · exact (leaf_eq_of_prefix T ha' ha h).symm
      subst a'
      have hbb : b = b' := List.append_cancel_left he
      subst b'
      rfl
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_leaves_graftTree T f q).mp hq
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, Subtype.ext hab⟩)

end WaveTurbulence.Induct
