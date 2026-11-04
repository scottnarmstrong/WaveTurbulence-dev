/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.LeafAddresses
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.PairInsertionLeaves

/-! # Exact global leaf sets after pair grafting (DH21 Proposition 4.8)

The proof uses COMB's literal address bijection, including the same-tree case.
-/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Every actual leaf supplies membership in its forest's global leaf set. -/
theorem forest_leaf_mem {w : ℕ} {tree : Fin w → TTree} (ℓ : GLeaf tree) :
    ℓ.1 ∈ forestSet tree TTree.leaves := (mem_forestSet tree).mpr ℓ.2

/-- Exact pair-graft leaf surgery, with all surviving and inserted addresses retained. -/
theorem graftPair_leaf_set {w : ℕ} (tree : Fin w → TTree) (ℓ q : GLeaf tree)
    (hq : q ≠ ℓ) (Q : Garden 2) :
    forestSet (Comb.graftLeafPairForest tree ℓ q hq (Q.tree 0) (Q.tree 1)) TTree.leaves =
      ((forestSet tree TTree.leaves \ {ℓ.1,q.1}) ∪ leafAddresses (Q.tree 0) ℓ.1) ∪
        leafAddresses (Q.tree 1) q.1 := by
  let E := Comb.pairInsertionLeafEquiv tree ℓ q hq Q
  ext z
  constructor
  · intro hz
    let zz : GLeaf (Comb.graftLeafPairForest tree ℓ q hq (Q.tree 0) (Q.tree 1)) :=
      ⟨z,(mem_forestSet _).mp hz⟩
    obtain ⟨u,hu⟩ := E.surjective zz
    cases u with
    | inl u =>
      have he := congrArg Subtype.val hu
      change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inl u)).1 = z at he
      rw [Comb.pairInsertionLeafEquiv_old] at he
      rw [← he]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨forest_leaf_mem u.1,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro (hl | hr)
      · exact u.2.1 (Subtype.ext hl)
      · exact u.2.2 (Subtype.ext hr)
    | inr u =>
      obtain ⟨v,rfl⟩ := (Comb.twoTreeLeafEquiv Q).surjective u
      cases v with
      | inl v =>
        have he := congrArg Subtype.val hu
        change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inr (Comb.twoTreeLeafEquiv Q (.inl v)))).1 = z at he
        rw [Comb.pairInsertionLeafEquiv_left] at he
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨v.1.2,v.2,he⟩
      | inr v =>
        have he := congrArg Subtype.val hu
        change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inr (Comb.twoTreeLeafEquiv Q (.inr v)))).1 = z at he
        rw [Comb.pairInsertionLeafEquiv_right] at he
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨v.1.2,v.2,he⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨hz,hne⟩ := Finset.mem_sdiff.mp hz
        let v : GLeaf tree := ⟨z,(mem_forestSet _).mp hz⟩
        have hl : v ≠ ℓ := fun h => hne (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val h)))
        have hr : v ≠ q := fun h => hne (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr (congrArg Subtype.val h))))
        let u : Comb.PairOutside tree ℓ q := ⟨v,hl,hr⟩
        have hh := forest_leaf_mem (E (.inl u))
        change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inl u)).1 ∈ _ at hh
        rw [Comb.pairInsertionLeafEquiv_old] at hh
        exact hh
      · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz
        let v : GLeaf (fun _ : Fin 1 => Q.tree 0) := ⟨(0,p),hp⟩
        have hh := forest_leaf_mem (E (.inr (Comb.twoTreeLeafEquiv Q (.inl v))))
        change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inr (Comb.twoTreeLeafEquiv Q (.inl v)))).1 ∈ _ at hh
        rw [Comb.pairInsertionLeafEquiv_left] at hh
        change addrExt ℓ.1 p ∈ _ at hh
        rw [he] at hh
        exact hh
    · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz
      let v : GLeaf (fun _ : Fin 1 => Q.tree 1) := ⟨(0,p),hp⟩
      have hh := forest_leaf_mem (E (.inr (Comb.twoTreeLeafEquiv Q (.inr v))))
      change (Comb.pairInsertionLeafEquiv tree ℓ q hq Q (.inr (Comb.twoTreeLeafEquiv Q (.inr v)))).1 ∈ _ at hh
      rw [Comb.pairInsertionLeafEquiv_right] at hh
      change addrExt q.1 p ∈ _ at hh
      rw [he] at hh
      exact hh

end WaveTurbulence.Reg
