/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairing

/-! # Collapsing an actual source subcouple to a new leaf pair

The forest surgery, outside matching and new opposite-sign pair are literal.
The operation retains every source mark outside the removed subcouple and adds
no mark at the new pair. It applies to any genuine embedded subcouple.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Source collapse as an actual full garden, with all surviving pairings retained. -/
noncomputable def collapseCoupleGarden {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) : Garden w :=
  let E := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  Comb.gardenFromLeafEquiv (collapsePairForest G.tree a b (Comb.subCouple_incomparable h)) G.sig
    (collapsedPairing h) E.symm (fun ℓ => by
      have hs := collapseLeafMap_sign h (E.symm ℓ)
      change nodeSign G.sig (E (E.symm ℓ)).1 = (collapsedPairing h).sign (E.symm ℓ) at hs
      rw [E.apply_symm_apply] at hs
      exact hs)

theorem collapseCoupleGarden_sig {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) : (collapseCoupleGarden h).sig = G.sig := rfl

theorem collapseCoupleGarden_tree {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) :
    (collapseCoupleGarden h).tree = collapsePairForest G.tree a b (Comb.subCouple_incomparable h) := rfl

/-- Exact compatibility of the new pairing with the complete leaf payload. -/
theorem collapseCoupleGarden_pair_payload {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (x : OutsideRoots G.tree a b ⊕ Fin 2) :
    (collapseCoupleGarden h).pair (collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) x) =
      collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) ((collapsedPairing h).pair x) := by
  let E := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  change E ((collapsedPairing h).pair (E.symm (E x))) = E ((collapsedPairing h).pair x)
  rw [Equiv.symm_apply_apply]

/-- All surviving original pairs remain exactly their old pairs. -/
theorem collapseCoupleGarden_pair_old {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (x : OutsideRoots G.tree a b) :
    (collapseCoupleGarden h).pair (collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) (.inl x)) =
      collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
        (.inl ⟨G.pair x.1,outsideRoots_closed G a b h x.1 x.2⟩) :=
  collapseCoupleGarden_pair_payload h (.inl x)

/-- The first new root is paired with the second new root. -/
theorem collapseCoupleGarden_pair_left {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) :
    (collapseCoupleGarden h).pair (collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) (.inr 0)) =
      collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) (.inr 1) :=
  collapseCoupleGarden_pair_payload h (.inr 0)

/-- The second new root is paired with the first new root. -/
theorem collapseCoupleGarden_pair_right {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) :
    (collapseCoupleGarden h).pair (collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) (.inr 1)) =
      collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h) (.inr 0) :=
  collapseCoupleGarden_pair_payload h (.inr 1)

/-- Ordinary source gardens remain ordinary under genuine subcouple collapse. -/
theorem collapseCoupleGarden_plain {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (hG : G.IsPlain) : (collapseCoupleGarden h).IsPlain := by
  intro ℓ
  let E := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  change (collapsedPairing h).mark (E.symm ℓ) = none
  cases E.symm ℓ with
  | inl x => exact hG x.1
  | inr i => rfl

/-- The source collapse removes exactly the branching nodes of the embedded subcouple. -/
theorem collapseCoupleGarden_order {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) :
    (collapseCoupleGarden h).order + (Comb.nodeSubtree a).order + (Comb.nodeSubtree b).order = G.order := by
  have ho := Comb.collapseSubCoupleForest_order h
  change (collapseCoupleGarden h).order + (Comb.subCoupleGarden h).order = G.order at ho
  rw [Comb.subCoupleGarden_order] at ho
  omega

end WaveTurbulence.Reg.Skeleton
