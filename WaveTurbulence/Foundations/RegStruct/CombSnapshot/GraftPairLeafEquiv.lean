/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.GraftLeafEquiv

/-! # Exact leaf bijection for pair insertion (TARGET L846–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree

variable {w : ℕ} (tree : Fin w → TTree)

abbrev PairOutside (ℓ q : GLeaf tree) := {x : GLeaf tree // x ≠ ℓ ∧ x ≠ q}

/-- Forget just the second excluded leaf. -/
@[expose] def forgetSecondLeaf (ℓ q : GLeaf tree) (s : TTree) :
    (PairOutside tree ℓ q ⊕ GLeaf (fun _ : Fin 1 => s)) →
      ({x : GLeaf tree // x ≠ ℓ} ⊕ GLeaf (fun _ : Fin 1 => s)) :=
  Sum.map (fun x => ⟨x.1, x.2.1⟩) id

theorem forgetSecondLeaf_injective (ℓ q : GLeaf tree) (s : TTree) :
    Function.Injective (forgetSecondLeaf tree ℓ q s) := by
  apply Function.Injective.sumMap
  · intro x y h
    apply Subtype.ext
    have hh := congrArg (fun z : {x : GLeaf tree // x ≠ ℓ} => z.1) h
    exact hh
  · exact Function.injective_id

/-- Surviving old leaves and the first inserted tree avoid the second graft slot. -/
@[expose] def firstGraftRemaining (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s : TTree) :
    (PairOutside tree ℓ q ⊕ GLeaf (fun _ : Fin 1 => s)) ↪
      {x : GLeaf (graftLeafForest tree ℓ s) // x ≠ graftLeafForest_other tree ℓ q hq s} where
  toFun x := ⟨graftLeafMap tree ℓ s (forgetSecondLeaf tree ℓ q s x), by
    intro h
    change graftLeafMap tree ℓ s (forgetSecondLeaf tree ℓ q s x) =
      graftLeafMap tree ℓ s (.inl ⟨q, hq⟩) at h
    have he := graftLeafMap_injective tree ℓ s h
    cases x with
    | inl x =>
      have he' : (⟨x.1, x.2.1⟩ : {a : GLeaf tree // a ≠ ℓ}) = ⟨q, hq⟩ := Sum.inl.inj he
      have hx := congrArg (fun z : {a : GLeaf tree // a ≠ ℓ} => z.1) he'
      exact x.2.2 hx
    | inr x =>
      change (Sum.inr x : {a : GLeaf tree // a ≠ ℓ} ⊕ GLeaf (fun _ : Fin 1 => s)) = .inl ⟨q, hq⟩ at he
      cases he⟩
  inj' := by
    intro x y h
    apply forgetSecondLeaf_injective tree ℓ q s
    apply graftLeafMap_injective tree ℓ s
    exact congrArg Subtype.val h

/-- Address-level forward map for all leaves after the two insertions. -/
@[expose] def graftPairLeafMap (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree) :
    ((PairOutside tree ℓ q ⊕ GLeaf (fun _ : Fin 1 => s)) ⊕ GLeaf (fun _ : Fin 1 => r)) →
      GLeaf (graftLeafPairForest tree ℓ q hq s r) :=
  fun x => graftLeafMap (graftLeafForest tree ℓ s) (graftLeafForest_other tree ℓ q hq s) r
    (Sum.map (firstGraftRemaining tree ℓ q hq s) id x)

theorem graftPairLeafMap_injective (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree) :
    Function.Injective (graftPairLeafMap tree ℓ q hq s r) :=
  (graftLeafMap_injective _ _ _).comp
    ((firstGraftRemaining tree ℓ q hq s).injective.sumMap Function.injective_id)

/-- Removing two distinct points lowers a finite cardinality by exactly two. -/
theorem card_pairOutside (ℓ q : GLeaf tree) (hq : q ≠ ℓ) :
    Fintype.card (PairOutside tree ℓ q) + 2 = Fintype.card (GLeaf tree) := by
  let e : PairOutside tree ℓ q ≃ {x : {x : GLeaf tree // x ≠ ℓ} // x ≠ ⟨q, hq⟩} :=
    { toFun x := ⟨⟨x.1, x.2.1⟩, fun he => x.2.2 (congrArg Subtype.val he)⟩
      invFun x := ⟨x.1.1, x.1.2, fun he => x.2 (Subtype.ext he)⟩
      left_inv x := by apply Subtype.ext; rfl
      right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl }
  have h1 := Fintype.card_congr (Equiv.optionSubtypeNe ℓ)
  have h2 := Fintype.card_congr (Equiv.optionSubtypeNe (⟨q, hq⟩ : {x : GLeaf tree // x ≠ ℓ}))
  have he := Fintype.card_congr e
  simp only [Fintype.card_option] at h1 h2
  omega

theorem graftPairLeafMap_card (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree) :
    Fintype.card ((PairOutside tree ℓ q ⊕ GLeaf (fun _ : Fin 1 => s)) ⊕ GLeaf (fun _ : Fin 1 => r)) =
      Fintype.card (GLeaf (graftLeafPairForest tree ℓ q hq s r)) := by
  have ho := card_pairOutside tree ℓ q hq
  have hs : Fintype.card (GLeaf (fun _ : Fin 1 => s)) = s.leaves.card := by
    rw [card_gleaf, card_leaves]
    simp only [Fin.sum_univ_one]
  have hr : Fintype.card (GLeaf (fun _ : Fin 1 => r)) = r.leaves.card := by
    rw [card_gleaf, card_leaves]
    simp only [Fin.sum_univ_one]
  have hn := graftLeafPairForest_leaves tree ℓ q hq s r
  simp only [Fintype.card_sum]
  omega

/-- The exact inherited/inserted leaf bijection for two graft slots. -/
@[expose] noncomputable def graftPairLeafEquiv (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree) :
    ((PairOutside tree ℓ q ⊕ GLeaf (fun _ : Fin 1 => s)) ⊕ GLeaf (fun _ : Fin 1 => r)) ≃
      GLeaf (graftLeafPairForest tree ℓ q hq s r) :=
  Equiv.ofBijective (graftPairLeafMap tree ℓ q hq s r)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨graftPairLeafMap_injective tree ℓ q hq s r, graftPairLeafMap_card tree ℓ q hq s r⟩)

/-- The first inserted leaf addresses are prefixed by the first slot address. -/
theorem graftPairLeafEquiv_left (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree)
    (x : GLeaf (fun _ : Fin 1 => s)) :
    (graftPairLeafEquiv tree ℓ q hq s r (.inl (.inr x))).1 = (ℓ.1.1, ℓ.1.2 ++ x.1.2) := rfl

/-- The second inserted leaf addresses are prefixed by the second slot address. -/
theorem graftPairLeafEquiv_right (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (s r : TTree)
    (x : GLeaf (fun _ : Fin 1 => r)) :
    (graftPairLeafEquiv tree ℓ q hq s r (.inr x)).1 = (q.1.1, q.1.2 ++ x.1.2) := rfl

end WaveTurbulence.Comb
