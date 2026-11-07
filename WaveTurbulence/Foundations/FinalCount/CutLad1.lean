/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.BetaCut
public import WaveTurbulence.Foundations.WaveB.Ladders
public import WaveTurbulence.Foundations.FinalCount.WorldFinalCountBetaCut
/-! Ladders under a cut (FINALCOUNT-G2 step 2, part 1): the ladders of the cut molecule are exactly the
ladders of `M` avoiding `v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two neighbour fibres fit in the degree. -/
theorem two_neighbor_bonds_le_degree (M : Molecule V D) {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : M.bondsBetween a b + M.bondsBetween a c ≤ M.deg a := by
  classical
  have hd : Disjoint (neighborDarts M a b) (neighborDarts M a c) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    exact hbc (((mem_neighborDarts M a b z).mp hz).2.symm.trans ((mem_neighborDarts M a c z).mp hw).2)
  have hsub : neighborDarts M a b ∪ neighborDarts M a c ⊆ M.dartsAt a := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact (mem_filter.mp hz).1
    · exact (mem_filter.mp hz).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, card_neighborDarts M hab, card_neighborDarts M hac] at hc
  exact hc

/-- Every atom of a ladder has degree at least `3`. -/
theorem ladder_deg_ge_three_u (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (h : N.IsLadder u w)
    (j : Fin (m + 1)) : 3 ≤ N.deg (u j) := by
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp h.2.1
  obtain ⟨k, hkj, hk⟩ := sourceLadder_u_single_neighbor N h j
  have h2 := h.2.2.2.1 j
  have hne1 : u j ≠ w j := fun e => huw j j e
  have hne2 : u j ≠ u k := fun e => hkj (hu e).symm
  have hne3 : w j ≠ u k := fun e => huw k j e.symm
  have := two_neighbor_bonds_le_degree N hne1 hne2 hne3
  omega

theorem ladder_deg_ge_three_w (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (h : N.IsLadder u w)
    (j : Fin (m + 1)) : 3 ≤ N.deg (w j) :=
  ladder_deg_ge_three_u N (sourceLadder_swap N h) j

theorem mem_ladderAtoms {m : ℕ} (u w : Fin (m + 1) → V) (a : V) :
    a ∈ Molecule.ladderAtoms u w ↔ ∃ j, u j = a ∨ w j = a := by
  classical
  unfold Molecule.ladderAtoms
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨j, Or.inl hj⟩
    · exact ⟨j, Or.inr hj⟩
  · rintro ⟨j, hj | hj⟩
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr ⟨j, hj⟩

theorem ladder_atom_deg_ge_three (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V}
    (h : N.IsLadder u w) {a : V} (ha : a ∈ Molecule.ladderAtoms u w) : 3 ≤ N.deg a := by
  obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms u w a).1 ha
  · rw [← hj]; exact ladder_deg_ge_three_u N h j
  · rw [← hj]; exact ladder_deg_ge_three_w N h j

section cut
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem cut_bonds' : (M.cut v v₂ x₁ x₂).bonds = M.bonds := rfl

theorem cut_atom_eq_iff (y : D) {a : V} (hav : a ≠ v) (hav₂ : a ≠ v₂) :
    (M.cut v v₂ x₁ x₂).atom y = a ↔ M.atom y = a := by
  rw [cut_atom]
  split_ifs with h
  · exact ⟨fun e => (hav₂ e.symm).elim, fun e => (hav (h.1 ▸ e.symm)).elim⟩
  · exact Iff.rfl

theorem cut_ends_eq_iff (x : D) {a b : V} (hav : a ≠ v) (hav₂ : a ≠ v₂) (hbv : b ≠ v) (hbv₂ : b ≠ v₂) :
    (M.cut v v₂ x₁ x₂).ends x = s(a, b) ↔ M.ends x = s(a, b) := by
  unfold Molecule.ends
  simp only [Sym2.eq_iff]
  have e1 := fun y => cut_atom_eq_iff M (x₁ := x₁) (x₂ := x₂) y hav hav₂
  have e2 := fun y => cut_atom_eq_iff M (x₁ := x₁) (x₂ := x₂) y hbv hbv₂
  have m1 : (M.cut v v₂ x₁ x₂).mate = M.mate := rfl
  show ((M.cut v v₂ x₁ x₂).atom x = a ∧ (M.cut v v₂ x₁ x₂).atom ((M.cut v v₂ x₁ x₂).mate x) = b ∨
      (M.cut v v₂ x₁ x₂).atom x = b ∧ (M.cut v v₂ x₁ x₂).atom ((M.cut v v₂ x₁ x₂).mate x) = a) ↔ _
  rw [m1, e1, e1, e2, e2]

theorem cut_bondsBetween_eq {a b : V} (hav : a ≠ v) (hav₂ : a ≠ v₂) (hbv : b ≠ v) (hbv₂ : b ≠ v₂) :
    (M.cut v v₂ x₁ x₂).bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  rw [cut_bonds' M]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  rw [cut_ends_eq_iff M x hav hav₂ hbv hbv₂]

theorem cut_directed_iff {a b : V} (hav : a ≠ v) (hav₂ : a ≠ v₂) (hbv : b ≠ v) (hbv₂ : b ≠ v₂) :
    (M.cut v v₂ x₁ x₂).Directed a b ↔ M.Directed a b := by
  unfold Molecule.Directed
  have e1 := fun y => cut_atom_eq_iff M (x₁ := x₁) (x₂ := x₂) y hav hav₂
  have e2 := fun y => cut_atom_eq_iff M (x₁ := x₁) (x₂ := x₂) y hbv hbv₂
  have m1 : (M.cut v v₂ x₁ x₂).mate = M.mate := rfl
  have o1 : (M.cut v v₂ x₁ x₂).out = M.out := rfl
  rw [m1, o1]
  simp only [e1, e2]

/-- A family avoiding `v` and `v₂`. -/
def Avoid (v v₂ : V) {m : ℕ} (u : Fin (m + 1) → V) : Prop := ∀ j, u j ≠ v ∧ u j ≠ v₂

theorem cut_isLadder_iff (hcd : M.IsCutData v v₂ x₁ x₂) {m : ℕ} {u w : Fin (m + 1) → V}
    (hu : Avoid v v₂ u) (hw : Avoid v v₂ w) :
    (M.cut v v₂ x₁ x₂).IsLadder u w ↔ M.IsLadder u w := by
  unfold Molecule.IsLadder
  have mem : ∀ a, a ≠ v₂ → (a ∈ (M.cut v v₂ x₁ x₂).atoms ↔ a ∈ M.atoms) := by
    intro a ha
    show a ∈ insert v₂ M.atoms ↔ _
    simp [ha]
  have key : ∀ (j : Fin (m + 1)) , True := fun _ => trivial
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_)))
  · refine forall_congr' fun j => ?_
    rw [mem _ (hu j).2, mem _ (hw j).2]
  · refine forall_congr' fun j => ?_
    rw [cut_bondsBetween_eq M (hu j).1 (hu j).2 (hw j).1 (hw j).2]
  · refine forall_congr' fun j => ?_
    rw [cut_bondsBetween_eq M (hu _).1 (hu _).2 (hu _).1 (hu _).2,
      cut_bondsBetween_eq M (hw _).1 (hw _).2 (hw _).1 (hw _).2,
      cut_directed_iff M (hu _).1 (hu _).2 (hu _).1 (hu _).2,
      cut_directed_iff M (hw _).1 (hw _).2 (hw _).1 (hw _).2]

end cut
end WaveTurbulence.FinalCount
