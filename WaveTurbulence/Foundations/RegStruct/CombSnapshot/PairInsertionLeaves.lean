/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.GraftPairLeafEquiv
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.TwoTreeLeaves

/-! # The literal old/new leaf payload of couple insertion (TARGET L846–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree

variable {w : ℕ} (tree : Fin w → TTree)

/-- Surviving old leaves plus the inserted couple's actual leaves parameterize the result. -/
@[expose] noncomputable def pairInsertionLeafEquiv (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (Q : Garden 2) :
    (PairOutside tree ℓ q ⊕ GLeaf Q.tree) ≃
      GLeaf (graftLeafPairForest tree ℓ q hq (Q.tree 0) (Q.tree 1)) :=
  ((Equiv.sumCongr (Equiv.refl _) (twoTreeLeafEquiv Q).symm).trans
    (Equiv.sumAssoc _ _ _).symm).trans
      (graftPairLeafEquiv tree ℓ q hq (Q.tree 0) (Q.tree 1))

/-- Old addresses are unchanged by the payload map. -/
theorem pairInsertionLeafEquiv_old (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (Q : Garden 2)
    (x : PairOutside tree ℓ q) :
    (pairInsertionLeafEquiv tree ℓ q hq Q (.inl x)).1 = x.1.1 := rfl

/-- The first inserted tree's leaves have the expected prefixed addresses. -/
theorem pairInsertionLeafEquiv_left (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (Q : Garden 2)
    (x : GLeaf (fun _ : Fin 1 => Q.tree 0)) :
    (pairInsertionLeafEquiv tree ℓ q hq Q (.inr (twoTreeLeafEquiv Q (.inl x)))).1 =
      (ℓ.1.1, ℓ.1.2 ++ x.1.2) := by
  simp only [pairInsertionLeafEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inr, Equiv.symm_apply_apply]
  exact graftPairLeafEquiv_left tree ℓ q hq _ _ x

/-- The second inserted tree's leaves have the expected prefixed addresses. -/
theorem pairInsertionLeafEquiv_right (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (Q : Garden 2)
    (x : GLeaf (fun _ : Fin 1 => Q.tree 1)) :
    (pairInsertionLeafEquiv tree ℓ q hq Q (.inr (twoTreeLeafEquiv Q (.inr x)))).1 =
      (q.1.1, q.1.2 ++ x.1.2) := by
  simp only [pairInsertionLeafEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inr, Equiv.symm_apply_apply]
  exact graftPairLeafEquiv_right tree ℓ q hq _ _ x

/-- Matching the two root signs preserves every leaf sign under insertion. -/
theorem pairInsertionLeafEquiv_sign (sig : Fin w → ℤˣ)
    (ℓ q : GLeaf tree) (hq : q ≠ ℓ) (Q : Garden 2)
    (h0 : Q.sig 0 = nodeSign sig ℓ.1) (h1 : Q.sig 1 = nodeSign sig q.1)
    (x : PairOutside tree ℓ q ⊕ GLeaf Q.tree) :
    nodeSign sig (pairInsertionLeafEquiv tree ℓ q hq Q x).1 =
      Sum.elim (fun y : PairOutside tree ℓ q => nodeSign sig y.1.1)
        (fun y : GLeaf Q.tree => nodeSign Q.sig y.1) x := by
  cases x with
  | inl x =>
    rw [pairInsertionLeafEquiv_old]
    rfl
  | inr x =>
    obtain ⟨y, rfl⟩ := (twoTreeLeafEquiv Q).surjective x
    cases y with
    | inl y =>
      rw [pairInsertionLeafEquiv_left]
      change pathSign (sig ℓ.1.1) (ℓ.1.2 ++ y.1.2) = pathSign (Q.sig 0) y.1.2
      rw [h0]
      exact pathSign_append _ _ _
    | inr y =>
      rw [pairInsertionLeafEquiv_right]
      change pathSign (sig q.1.1) (q.1.2 ++ y.1.2) = pathSign (Q.sig 1) y.1.2
      rw [h1]
      exact pathSign_append _ _ _

end WaveTurbulence.Comb
