/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.RootedFrameExtraction

/-! # Property L at literal global addresses -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Address form of the source property L. -/
def ExternalAt {w : ℕ} (G : Garden w) (a : Fin w × Path) : Prop :=
  ∃ ℓ : GLeaf G.tree, Below a ℓ.1 ∧ (G.pair ℓ).1.1 ≠ a.1

/-- The address predicate is exactly property L at an actual node. -/
theorem externalAt_iff_hasExternal {w : ℕ} (G : Garden w) (a : GNode G.tree) :
    ExternalAt G a.1 ↔ HasExternal G a := by
  constructor
  · rintro ⟨ℓ,hℓ,hp⟩
    refine ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hp⟩
    exact ⟨hℓ.1.symm,hℓ.2⟩
  · rintro ⟨ℓ,hℓ,hp⟩
    have hd := (Finset.mem_filter.mp hℓ).2
    exact ⟨ℓ,⟨hd.1.symm,hd.2⟩,hp⟩

/-- Property L passes from a rooted subtree to every ancestor of that subtree. -/
theorem ExternalAt.ancestor {w : ℕ} {G : Garden w} {a b : Fin w × Path}
    (h : ExternalAt G b) (hab : Below a b) : ExternalAt G a := by
  obtain ⟨ℓ,hℓ,hp⟩ := h
  exact ⟨ℓ,below_trans hab hℓ,fun he => hp (he.trans hab.1.symm)⟩

/-- Existence of an actual completely paired sub-couple at two literal roots. -/
def SubCoupleAt {w : ℕ} (G : Garden w) (a b : Fin w × Path) : Prop :=
  ∃ A B : GNode G.tree, A.1 = a ∧ B.1 = b ∧ Comb.IsSubCouple G A B

/-- Actual extraction and pair-block inclusion produce an address-indexed sub-couple. -/
theorem subCoupleAt_of_decoded_block (Q C : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a b : Fin 2 × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1) b.2 = some C.trees.2)
    (hP : ∀ p ∈ C.pairsAt a b, p ∈ Q.raw.2) : SubCoupleAt G a b := by
  let A : GNode G.tree := ⟨a,(Comb.subtree_exists_iff _ _).mp ⟨_,ha⟩⟩
  let B : GNode G.tree := ⟨b,(Comb.subtree_exists_iff _ _).mp ⟨_,hb⟩⟩
  exact ⟨A,B,rfl,rfl,subCouple_of_decoded_block Q C G hG A B ha hb hP⟩

/-- An actual sub-couple across the two original trees supplies property L. -/
theorem SubCoupleAt.external {w : ℕ} {G : Garden w} {a b : Fin w × Path}
    (h : SubCoupleAt G a b) (hj : b.1 ≠ a.1) : ExternalAt G a := by
  obtain ⟨A,B,rfl,rfl,h⟩ := h
  exact (externalAt_iff_hasExternal G A).mpr (hasExternal_of_subCouple h hj)

/-- An actual side couple lying in one original tree has no property L. -/
theorem SubCoupleAt.not_external {w : ℕ} {G : Garden w} {a b : Fin w × Path}
    (h : SubCoupleAt G a b) (hj : b.1 = a.1) : ¬ ExternalAt G a := by
  obtain ⟨A,B,rfl,rfl,h⟩ := h
  exact fun he => not_hasExternal_of_subCouple h hj ((externalAt_iff_hasExternal G A).mp he)

/-- The two roots of an actual sub-couple can be exchanged. -/
theorem SubCoupleAt.symm {w : ℕ} {G : Garden w} {a b : Fin w × Path}
    (h : SubCoupleAt G a b) : SubCoupleAt G b a := by
  obtain ⟨A,B,hA,hB,h⟩ := h
  exact ⟨B,A,hB,hA,by simpa only [Comb.IsSubCouple,Finset.union_comm] using h⟩

end WaveTurbulence.Reg
