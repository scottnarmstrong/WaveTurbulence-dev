/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-! # Literal leaf addresses and endpoints of source pair lists (DH21 Proposition 4.8) -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- The actual leaf addresses below an arbitrary global root. -/
def leafAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) : Finset (Fin w × Path) :=
  t.leaves.image (addrExt a)

/-- All endpoints of a source pair list. -/
def pairEndpoints {α : Type*} [DecidableEq α] (P : List (α × α)) : Finset α :=
  (P.map Prod.fst).toFinset ∪ (P.map Prod.snd).toFinset

@[simp] theorem leafAddresses_leaf {w : ℕ} (a : Fin w × Path) :
    leafAddresses .leaf a = {a} := by simp [leafAddresses, TTree.leaves, addrExt]

/-- Rooted address transport is literal prefix concatenation. -/
theorem addrExt_cons {w : ℕ} (a : Fin w × Path) (i : Fin 3) (p : Path) :
    addrExt a (i :: p) = addrExt (addrExt a [i]) p := by
  rw [addrExt_append]
  rfl

/-- Leaf sets decompose over the three child roots. -/
theorem leafAddresses_node {w : ℕ} (l m r : TTree) (a : Fin w × Path) :
    leafAddresses (.node l m r) a =
      leafAddresses l (addrExt a [0]) ∪ leafAddresses m (addrExt a [1]) ∪
        leafAddresses r (addrExt a [2]) := by
  simp only [leafAddresses, TTree.leaves, Finset.image_union, TTree.pre,
    Finset.image_image, Function.comp_def]
  have h0 : (fun p => addrExt a ((0 : Fin 3) :: p)) = addrExt (addrExt a [0]) :=
    funext (addrExt_cons a 0)
  have h1 : (fun p => addrExt a ((1 : Fin 3) :: p)) = addrExt (addrExt a [1]) :=
    funext (addrExt_cons a 1)
  have h2 : (fun p => addrExt a ((2 : Fin 3) :: p)) = addrExt (addrExt a [2]) :=
    funext (addrExt_cons a 2)
  rw [h0,h1,h2]

/-- Membership in endpoints is membership as one coordinate of an actual listed pair. -/
theorem mem_pairEndpoints_iff {α : Type*} [DecidableEq α] (P : List (α × α)) (x : α) :
    x ∈ pairEndpoints P ↔ ∃ p ∈ P, x = p.1 ∨ x = p.2 := by
  simp only [pairEndpoints, Finset.mem_union, List.mem_toFinset, List.mem_map]
  constructor
  · rintro (⟨p,hp,hx⟩ | ⟨p,hp,hx⟩)
    · exact ⟨p,hp,Or.inl hx.symm⟩
    · exact ⟨p,hp,Or.inr hx.symm⟩
  · rintro ⟨p,hp,hx | hx⟩
    · exact Or.inl ⟨p,hp,hx.symm⟩
    · exact Or.inr ⟨p,hp,hx.symm⟩

@[simp] theorem pairEndpoints_nil {α : Type*} [DecidableEq α] :
    pairEndpoints ([] : List (α × α)) = ∅ := by simp [pairEndpoints]

@[simp] theorem pairEndpoints_singleton {α : Type*} [DecidableEq α] (a b : α) :
    pairEndpoints [(a,b)] = {a,b} := by ext x; simp [pairEndpoints]

/-- Appending pair lists takes the union of their actual endpoints. -/
theorem pairEndpoints_append {α : Type*} [DecidableEq α] (P Q : List (α × α)) :
    pairEndpoints (P ++ Q) = pairEndpoints P ∪ pairEndpoints Q := by
  ext x
  simp only [pairEndpoints, List.map_append, List.toFinset_append, Finset.mem_union]
  tauto

end WaveTurbulence.Reg
