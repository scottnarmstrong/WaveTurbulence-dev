/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeNodes

/-! # Separation of code blocks by their rooted addresses -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Two raw rooted subtrees have incomparable global roots. -/
def IncompAddr {w : ℕ} (a b : Fin w × Path) : Prop := ¬ Below a b ∧ ¬ Below b a

theorem IncompAddr.symm {w : ℕ} {a b : Fin w × Path} (h : IncompAddr a b) : IncompAddr b a :=
  ⟨h.2,h.1⟩

/-- Descending into disjoint rooted subtrees preserves incomparability. -/
theorem IncompAddr.descendants {w : ℕ} {a b x y : Fin w × Path} (h : IncompAddr a b)
    (hx : Below a x) (hy : Below b y) : IncompAddr x y := by
  constructor
  · intro hxy
    exact (below_comparable (below_trans hx hxy) hy).elim h.1 h.2
  · intro hyx
    exact (below_comparable hx (below_trans hy hyx)).elim h.1 h.2

/-- Prefix comparisons below the same global root reduce to the relative paths. -/
theorem below_same_root {w : ℕ} (a : Fin w × Path) (p q : Path) :
    Below (addrExt a p) (addrExt a q) ↔ p <+: q := by
  simp only [Below,addrExt,List.prefix_append_right_inj,true_and]

/-- Distinct children have disjoint entire descendant subtrees. -/
theorem incomp_distinct_children {w : ℕ} (a : Fin w × Path) (i j : Fin 3) (p q : Path)
    (hij : i ≠ j) : IncompAddr (addrExt a (i :: p)) (addrExt a (j :: q)) := by
  constructor
  · intro h
    exact hij (List.cons_prefix_cons.mp ((below_same_root a _ _).mp h)).1
  · intro h
    exact hij.symm (List.cons_prefix_cons.mp ((below_same_root a _ _).mp h)).1

/-- Node sets in two incomparable rooted blocks cannot meet. -/
theorem not_mem_coupleNodes_of_below {w : ℕ} (Q : RegCpl) {r a b z : Fin w × Path}
    (hz : Below r z) (ha : IncompAddr r a) (hb : IncompAddr r b) :
    z ∉ coupleNodes Q a b := by
  intro h
  rcases coupleNodes_below Q a b z h with hza | hzb
  · exact (below_comparable hz hza).elim ha.1 ha.2
  · exact (below_comparable hz hzb).elim hb.1 hb.2

/-- A chain's entire represented set is confined to its rooted subtree. -/
theorem not_mem_chainNodes_of_below {w : ℕ} (X : RegChain) (ζ : ℤˣ) {r a z : Fin w × Path}
    (hz : Below r z) (ha : IncompAddr r a) : z ∉ chainNodes X ζ a := by
  intro h
  exact (below_comparable hz (chainNodes_below X ζ a z h)).elim ha.1 ha.2

/-- A proper child-descendant cannot equal its parent root. -/
theorem below_child_ne_root {w : ℕ} (a z : Fin w × Path) (i : Fin 3) (p : Path)
    (h : Below (addrExt a (i :: p)) z) : z ≠ a := by
  intro he
  have hl := h.2.length_le
  rw [he] at hl
  change (a.2 ++ i :: p).length ≤ a.2.length at hl
  simp only [List.length_append,List.length_cons] at hl
  omega

/-- Relocation is locally compatible below any root that is not an ancestor of the insertion. -/
theorem relocate_respectsAt_of_not_below (target root : Fin 2 × Path) (c l : Fin 3)
    (h : ¬ Below root target) : RespectsAt (RawCpl.relocate target c l) root := by
  by_cases ht : Below target root
  · exact relocate_respects_desc target root c l ht
  · exact relocate_respects_incomparable target root c l ht h

/-- The mini-tree table separates its continuation, red and green slots at both branching nodes. -/
theorem miniTree_slots_separate (m : MiniTreeCode) :
    m.red.1 ≠ m.c ∧ m.green.1 ≠ m.c ∧ m.red.1 ≠ m.green.1 ∧
      m.red.2 ≠ m.lone ∧ m.green.2 ≠ m.lone ∧ m.red.2 ≠ m.green.2 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

end WaveTurbulence.Reg
