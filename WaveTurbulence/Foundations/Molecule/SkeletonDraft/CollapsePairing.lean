/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseLeafPayload

/-! # Signed matching payload for collapsing an actual embedded source couple -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Raw address containment is exactly the source's descendant-leaf predicate. -/
theorem leafBelow_iff_below {w : ℕ} {tree : Fin w → TTree} (a : GNode tree) (ℓ : GLeaf tree) :
    ℓ ∈ a.leavesBelow ↔ Below a.1 ℓ.1 := by
  rw [GNode.leavesBelow,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  change (a.1.1 = ℓ.1.1 ∧ a.1.2 <+: ℓ.1.2) ↔ (ℓ.1.1 = a.1.1 ∧ a.1.2 <+: ℓ.1.2)
  exact and_congr eq_comm Iff.rfl

/-- The complement of a completely paired family is closed under the original involution. -/
theorem paired_complement_closed {w : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (hS : G.CompletelyPaired S) (ℓ : GLeaf G.tree) (hℓ : ℓ ∉ S) : G.pair ℓ ∉ S := by
  intro hp
  have hh := (hS (G.pair ℓ) hp).2
  rw [G.pair_pair] at hh
  exact hℓ hh

/-- Deleting both subcouple roots leaves all surviving original leaves paired among themselves. -/
theorem outsideRoots_closed {w : ℕ} (G : Garden w) (a b : GNode G.tree) (h : Comb.IsSubCouple G a b)
    (ℓ : GLeaf G.tree) (hℓ : ¬ Below a.1 ℓ.1 ∧ ¬ Below b.1 ℓ.1) :
    ¬ Below a.1 (G.pair ℓ).1 ∧ ¬ Below b.1 (G.pair ℓ).1 := by
  have hn : ℓ ∉ a.leavesBelow ∪ b.leavesBelow := by
    intro hm
    rcases Finset.mem_union.mp hm with ha | hb
    · exact hℓ.1 ((leafBelow_iff_below a ℓ).mp ha)
    · exact hℓ.2 ((leafBelow_iff_below b ℓ).mp hb)
  have hp := paired_complement_closed G _ h ℓ hn
  constructor
  · intro ha
    exact hp (Finset.mem_union_left _ ((leafBelow_iff_below a (G.pair ℓ)).mpr ha))
  · intro hb
    exact hp (Finset.mem_union_right _ ((leafBelow_iff_below b (G.pair ℓ)).mpr hb))

/-- The newly created opposite-sign root pair, at either original orientation. -/
def rootPairing (ζ : ℤˣ) : Comb.SignedPairing (Fin 2) where
  sign i := if i = 0 then ζ else -ζ
  pair i := 1-i
  mark _ := none
  pair_pair i := by fin_cases i <;> rfl
  pair_eq_iff i := by fin_cases i <;> decide
  pair_sign i _ := by fin_cases i <;> simp

/-- The complete collapsed matching consists of the unchanged outside pairs and one new root pair. -/
def collapsedPairing {w : ℕ} {G : Garden w} {a b : GNode G.tree} (h : Comb.IsSubCouple G a b) :
    Comb.SignedPairing (OutsideRoots G.tree a b ⊕ Fin 2) :=
  ((Comb.gardenPairing G).subtype (fun ℓ => ¬ Below a.1 ℓ.1 ∧ ¬ Below b.1 ℓ.1)
    (outsideRoots_closed G a b h)).sum (rootPairing (G.sign a))

/-- The actual source root-sign identity makes every payload sign agree with its new leaf address. -/
theorem collapseLeafMap_sign {w : ℕ} {G : Garden w} {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (x : OutsideRoots G.tree a b ⊕ Fin 2) :
    nodeSign G.sig (collapseLeafMap G.tree a b (Comb.subCouple_incomparable h) x).1 = (collapsedPairing h).sign x := by
  cases x with
  | inl ℓ => rfl
  | inr i =>
    fin_cases i
    · rfl
    · exact Comb.subCouple_sign h

end WaveTurbulence.Reg.Skeleton
