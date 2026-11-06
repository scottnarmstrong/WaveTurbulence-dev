/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolLadder
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
import Mathlib.Tactic
/-! Tree facts for the garden molecule: a non-root branch is a child of its parent, the parent is
unique, and an interior ladder atom (degree four) has its parent among its three bond neighbours. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LadderDisjoint WaveTurbulence.Mole
variable {w : ℕ} {tree : Fin w → TTree}

theorem isChildOf_parent (c : GBranch tree) (hc : c.1.2 ≠ []) :
    c.IsChildOf (GNode.parent c.toNode hc) := by
  refine ⟨rfl, c.1.2.getLast hc, ?_⟩
  change c.1.2 = c.1.2.dropLast ++ [c.1.2.getLast hc]
  rw [List.dropLast_append_getLast]

theorem isChildOf_ne_nil {c p : GBranch tree} (h : c.IsChildOf p) : c.1.2 ≠ [] := by
  obtain ⟨_, i, hi⟩ := h
  rw [hi]; simp

theorem isChildOf_eq_parent {c p : GBranch tree} (h : c.IsChildOf p) :
    p = GNode.parent c.toNode (isChildOf_ne_nil h) := by
  obtain ⟨h1, i, hi⟩ := h
  apply Subtype.ext
  apply Prod.ext
  · exact h1.symm
  · change p.1.2 = c.1.2.dropLast
    rw [hi]; simp

theorem isChildOf_unique {c p p' : GBranch tree} (h : c.IsChildOf p) (h' : c.IsChildOf p') : p = p' := by
  rw [isChildOf_eq_parent h, isChildOf_eq_parent h']

theorem isChildOf_length {c p : GBranch tree} (h : c.IsChildOf p) : p.1.2.length < c.1.2.length := by
  obtain ⟨_, i, hi⟩ := h
  rw [hi]; simp

theorem deg_interior {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    {a b c e : V} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h2 : M.bondsBetween a b = 2) (h1 : M.bondsBetween a c = 1) (h3 : M.bondsBetween a e = 1)
    (hd : M.deg a ≤ 4) : M.deg a = 4 := by
  have hdis1 := disjoint_neighborDarts M a hbc
  have hdis2 : Disjoint (neighborDarts M a b ∪ neighborDarts M a c) (neighborDarts M a e) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_neighborDarts M a hbe, disjoint_neighborDarts M a hce⟩
  have hcard : (neighborDarts M a b ∪ neighborDarts M a c ∪ neighborDarts M a e).card = 4 := by
    rw [Finset.card_union_of_disjoint hdis2, Finset.card_union_of_disjoint hdis1,
      card_neighborDarts M hab, card_neighborDarts M hac, card_neighborDarts M hae, h2, h1, h3]
  unfold Molecule.deg
  rw [dartsAt_interior M hab hac hae hbc hbe hce h2 h1 h3 hd, hcard]

theorem parent_mem_interior (G : Garden w) {a b c e : GBranch G.tree} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h2 : G.molecule.bondsBetween a b = 2) (h1 : G.molecule.bondsBetween a c = 1)
    (h3 : G.molecule.bondsBetween a e = 1) :
    ∃ hc : a.1.2 ≠ [], GNode.parent a.toNode hc = b ∨ GNode.parent a.toNode hc = c ∨
      GNode.parent a.toNode hc = e := by
  have hd := garden_molecule_deg_le_four G a
  have h4 := deg_interior G.molecule hab hac hae hbc hbe hce h2 h1 h3 hd
  have hc : a.1.2 ≠ [] := by
    intro h
    have := root_degree_le_three G a h
    omega
  refine ⟨hc, ?_⟩
  obtain ⟨x, hxa, hxm⟩ := branch_adj_parent G a hc
  have hx : x ∈ G.molecule.dartsAt a := by
    unfold Molecule.dartsAt; simp [hxa]
  rw [dartsAt_interior G.molecule hab hac hae hbc hbe hce h2 h1 h3 hd] at hx
  simp only [Finset.mem_union, mem_neighborDarts'] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl (hxm.symm.trans hx.2)
  · exact Or.inr (Or.inl (hxm.symm.trans hx.2))
  · exact Or.inr (Or.inr (hxm.symm.trans hx.2))

theorem no_peak (G : Garden w) {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree}
    (hL : G.molecule.IsLadder u v) (t : GBranch G.tree → ℝ)
    (ht : ∀ b' b : GBranch G.tree, b'.IsChildOf b → t b' < t b) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) :
    max (t (rowN u j)) (t (rowN v j)) < max (t (rowN u (j - 1))) (t (rowN v (j - 1))) ∨
    max (t (rowN u j)) (t (rowN v j)) < max (t (rowN u (j + 1))) (t (rowN v (j + 1))) := by
  have hjm1 : j - 1 + 1 = j := by omega
  have hl := ladderN_rail G.molecule hL (show j - 1 < m by omega)
  rw [hjm1] at hl
  have hr := ladderN_rail G.molecule hL hjm
  have hjle : j ≤ m := hjm.le
  have hd1 : j - 1 ≤ m := by omega
  have hd2 : j + 1 ≤ m := by omega
  have hl1 : G.molecule.bondsBetween (rowN u j) (rowN u (j - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.1
  have hl2 : G.molecule.bondsBetween (rowN v j) (rowN v (j - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.2.1
  have hrung := ladderN_rung G.molecule hL hjle
  have hrung' : G.molecule.bondsBetween (rowN v j) (rowN u j) = 2 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hrung
  by_cases hcase : t (rowN v j) ≤ t (rowN u j)
  · have hmax : max (t (rowN u j)) (t (rowN v j)) = t (rowN u j) := max_eq_left hcase
    rw [hmax]
    obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN u j) (b := rowN v j) (c := rowN u (j - 1))
      (e := rowN u (j + 1)) (ladderN_uv G.molecule hL hjle hjle) (ladderN_uu G.molecule hL hjle hd1 (by omega))
      (ladderN_uu G.molecule hL hjle hd2 (by omega)) (Ne.symm (ladderN_uv G.molecule hL hd1 hjle))
      (Ne.symm (ladderN_uv G.molecule hL hd2 hjle)) (ladderN_uu G.molecule hL hd1 hd2 (by omega))
      hrung hl1 hr.1
    have hlt := ht _ _ (isChildOf_parent (rowN u j) hc)
    rcases hp with hp | hp | hp
    · rw [hp] at hlt; exact absurd hlt (not_lt.mpr hcase)
    · left; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_left _ _)
    · right; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_left _ _)
  · have hcase' : t (rowN u j) < t (rowN v j) := not_le.mp hcase
    have hmax : max (t (rowN u j)) (t (rowN v j)) = t (rowN v j) := max_eq_right hcase'.le
    rw [hmax]
    obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN v j) (b := rowN u j) (c := rowN v (j - 1))
      (e := rowN v (j + 1)) (Ne.symm (ladderN_uv G.molecule hL hjle hjle))
      (ladderN_vv G.molecule hL hjle hd1 (by omega)) (ladderN_vv G.molecule hL hjle hd2 (by omega))
      (ladderN_uv G.molecule hL hjle hd1) (ladderN_uv G.molecule hL hjle hd2)
      (ladderN_vv G.molecule hL hd1 hd2 (by omega)) hrung' hl2 hr.2.1
    have hlt := ht _ _ (isChildOf_parent (rowN v j) hc)
    rcases hp with hp | hp | hp
    · rw [hp] at hlt; exact absurd hlt (not_lt.mpr hcase'.le)
    · left; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_right _ _)
    · right; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_right _ _)

end WaveTurbulence.Ladder
