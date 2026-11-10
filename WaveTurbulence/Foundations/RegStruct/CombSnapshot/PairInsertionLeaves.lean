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

end WaveTurbulence.Comb
