/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
public import WaveTurbulence.Foundations.Molecule.VineBalancedCuts
import Mathlib.Tactic

/-! # VINE-RHO (3): flow along an inserted rung chain

For a full rung sequence `Q` of `k` rungs in a molecule of degree `≤ 4`, whose atoms carry labels `φ`
(`u_i ↦ N + i - 1`, `v_i ↦ N + k + i - 1`, the four end atoms below `N`), with every inserted atom balanced
(in-degree equal to out-degree), the quantity `α_i + β_i` (net outflow of the two rails after rung `i`) is
constant along the chain. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine Finset
set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Four incidences -/

theorem FI_cases (M : Molecule V D) (hM : M.IsMolecule) {v : V} {nb : Fin 4 → V}
    (R : FourIncidences M v nb) {z : D} (hz : M.atom z = v) : ∃ j, R.dart j = z := by
  have : z ∈ univ.image R.dart := by
    rw [fourIncidences_image M hM R]; exact (Mole.mem_dartsAt M v z).mpr hz
  obtain ⟨j, _, hj⟩ := mem_image.mp this
  exact ⟨j, hj⟩

theorem FI_sum_signs (M : Molecule V D) (hM : M.IsMolecule) {v : V} {nb : Fin 4 → V}
    (R : FourIncidences M v nb) (hbal : M.outdeg v = M.indeg v) :
    M.dartSign (R.dart 0) + M.dartSign (R.dart 1) + M.dartSign (R.dart 2) + M.dartSign (R.dart 3) = 0 := by
  have h := signed_degree M v
  rw [← fourIncidences_image M hM R, Finset.sum_image (fun i _ j _ hij => R.injective hij),
    Fin.sum_univ_four] at h
  simp only [smul_eq_mul, mul_one, hbal, sub_self] at h
  exact h

theorem FI_card_to (M : Molecule V D) (hM : M.IsMolecule) {v : V} {nb : Fin 4 → V}
    (R : FourIncidences M v nb) (w : V) :
    (univ.filter (fun d => M.atom d = v ∧ M.atom (M.mate d) = w)).card =
      (univ.filter (fun j : Fin 4 => nb j = w)).card := by
  have : univ.filter (fun d => M.atom d = v ∧ M.atom (M.mate d) = w) =
      (univ.filter (fun j : Fin 4 => nb j = w)).image R.dart := by
    ext d
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨j, rfl⟩ := FI_cases M hM R h1
      exact ⟨j, by rw [← R.neighbor_eq]; exact h2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨R.atom_eq j, by rw [R.neighbor_eq]; exact hj⟩
  rw [this, card_image_of_injective _ R.injective]

/-! ## Labelled chains -/

variable (M : Molecule V D) {k : ℕ} (Q : FullRungSequence M k) (φ : V → ℕ) (N : ℕ)

structure Lab : Prop where
  u : ∀ i, 1 ≤ i → i ≤ k → φ (Q.u i) = N + (i - 1)
  v : ∀ i, 1 ≤ i → i ≤ k → φ (Q.v i) = N + k + (i - 1)
  lo : φ (Q.u 0) < N ∧ φ (Q.v 0) < N ∧ φ (Q.u (k + 1)) < N ∧ φ (Q.v (k + 1)) < N

variable {M Q φ N}

theorem Lab.Pu (hl : Lab M Q φ N) (i : ℕ) (hi : i ≤ k + 1) :
    φ (Q.u i) < N ∨ (1 ≤ i ∧ i ≤ k ∧ φ (Q.u i) = N + (i - 1)) := by
  by_cases h0 : i = 0
  · subst h0; exact Or.inl hl.lo.1
  by_cases h1 : i = k + 1
  · subst h1; exact Or.inl hl.lo.2.2.1
  exact Or.inr ⟨by omega, by omega, hl.u i (by omega) (by omega)⟩

theorem Lab.Pv (hl : Lab M Q φ N) (i : ℕ) (hi : i ≤ k + 1) :
    φ (Q.v i) < N ∨ (1 ≤ i ∧ i ≤ k ∧ φ (Q.v i) = N + k + (i - 1)) := by
  by_cases h0 : i = 0
  · subst h0; exact Or.inl hl.lo.2.1
  by_cases h1 : i = k + 1
  · subst h1; exact Or.inl hl.lo.2.2.2
  exact Or.inr ⟨by omega, by omega, hl.v i (by omega) (by omega)⟩

theorem ne_of_phi {x y : V} (h : φ x ≠ φ y) : x ≠ y := fun e => h (congrArg φ e)

/-- the key distinctness facts, all by label arithmetic -/
theorem Lab.uv_ne (hl : Lab M Q φ N) {i j : ℕ} (hi : i ≤ k + 1) (hj : j ≤ k + 1)
    (hi' : 1 ≤ i ∧ i ≤ k) : Q.u i ≠ Q.v j := by
  refine ne_of_phi (φ := φ) ?_
  have := hl.u i hi'.1 hi'.2
  rcases hl.Pv j hj with h' | h' <;> omega

theorem Lab.vu_ne (hl : Lab M Q φ N) {i j : ℕ} (hi : i ≤ k + 1) (hj : j ≤ k + 1)
    (hi' : 1 ≤ i ∧ i ≤ k) : Q.v i ≠ Q.u j := by
  refine ne_of_phi (φ := φ) ?_
  have := hl.v i hi'.1 hi'.2
  rcases hl.Pu j hj with h' | h' <;> omega

theorem Lab.uu_ne (hl : Lab M Q φ N) {i j : ℕ} (hi : i ≤ k + 1) (hj : j ≤ k + 1)
    (hi' : 1 ≤ i ∧ i ≤ k) (hij : i ≠ j) : Q.u i ≠ Q.u j := by
  refine ne_of_phi (φ := φ) ?_
  have := hl.u i hi'.1 hi'.2
  rcases hl.Pu j hj with h' | h' <;> omega

theorem Lab.vv_ne (hl : Lab M Q φ N) {i j : ℕ} (hi : i ≤ k + 1) (hj : j ≤ k + 1)
    (hi' : 1 ≤ i ∧ i ≤ k) (hij : i ≠ j) : Q.v i ≠ Q.v j := by
  refine ne_of_phi (φ := φ) ?_
  have := hl.v i hi'.1 hi'.2
  rcases hl.Pv j hj with h' | h' <;> omega

/-! ## Rung cancellation -/

variable (hM : M.IsMolecule)
include hM

/-- the two rung darts of `u_i` are the mates of the two rung darts of `v_i` -/
theorem rung_signs (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k) :
    M.dartSign ((Q.upper i h1 h2).dart 0) + M.dartSign ((Q.upper i h1 h2).dart 1) +
      (M.dartSign ((Q.lower i h1 h2).dart 0) + M.dartSign ((Q.lower i h1 h2).dart 1)) = 0 := by
  set U := Q.upper i h1 h2
  set L := Q.lower i h1 h2
  have key : ∀ c : Fin 4, c = 0 ∨ c = 1 → ∃ j : Fin 4, (j = 0 ∨ j = 1) ∧ M.mate (U.dart c) = L.dart j := by
    intro c hc
    have hat : M.atom (M.mate (U.dart c)) = Q.v i := by
      rw [U.neighbor_eq]; rcases hc with rfl | rfl <;> rfl
    obtain ⟨j, hj⟩ := FI_cases M hM L hat
    refine ⟨j, ?_, hj.symm⟩
    have hn : M.atom (M.mate (L.dart j)) = Q.u i := by
      rw [hj, M.mate_mate, U.atom_eq]
    rw [L.neighbor_eq] at hn
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      exact hl.uv_ne (i := i) (j := i - 1) (by omega) (by omega) ⟨h1, h2⟩ hn.symm
    · exfalso
      exact hl.uv_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, h2⟩ hn.symm
  obtain ⟨j0, hj0, e0⟩ := key 0 (Or.inl rfl)
  obtain ⟨j1, hj1, e1⟩ := key 1 (Or.inr rfl)
  have hne : j0 ≠ j1 := by
    intro h
    subst h
    have := Mole.mate_injective M (e0.trans e1.symm)
    exact absurd (U.injective this) (by decide)
  have s0 := Mole.dartSign_mate M (U.dart 0)
  have s1 := Mole.dartSign_mate M (U.dart 1)
  rw [e0] at s0
  rw [e1] at s1
  rcases hj0 with rfl | rfl <;> rcases hj1 with rfl | rfl
  · exact absurd rfl hne
  · linarith
  · linarith
  · exact absurd rfl hne


/-- balance of the rail darts at one rung pair -/
theorem rail_balance (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k)
    (hbu : M.outdeg (Q.u i) = M.indeg (Q.u i)) (hbv : M.outdeg (Q.v i) = M.indeg (Q.v i)) :
    M.dartSign ((Q.upper i h1 h2).dart 2) + M.dartSign ((Q.upper i h1 h2).dart 3) +
      (M.dartSign ((Q.lower i h1 h2).dart 2) + M.dartSign ((Q.lower i h1 h2).dart 3)) = 0 := by
  have a := FI_sum_signs M hM (Q.upper i h1 h2) hbu
  have b := FI_sum_signs M hM (Q.lower i h1 h2) hbv
  have c := rung_signs hM hl i h1 h2
  linarith

/-- consecutive upper rail darts are mates -/
theorem link_upper (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    M.mate ((Q.upper i h1 (by omega)).dart 3) = (Q.upper (i + 1) (by omega) h2).dart 2 := by
  set U := Q.upper i h1 (by omega)
  set U' := Q.upper (i + 1) (by omega) h2
  have hat : M.atom (M.mate (U.dart 3)) = Q.u (i + 1) := by
    rw [U.neighbor_eq]; rfl
  obtain ⟨j, hj⟩ := FI_cases M hM U' hat
  have hn : M.atom (M.mate (U'.dart j)) = Q.u i := by
    rw [hj, M.mate_mate, U.atom_eq]
  rw [U'.neighbor_eq] at hn
  rw [← hj]
  fin_cases j
  · exfalso; exact hl.uv_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hn.symm
  · exfalso; exact hl.uv_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hn.symm
  · rfl
  · exfalso; exact hl.uu_ne (i := i) (j := i + 2) (by omega) (by omega) ⟨h1, by omega⟩ (by omega) hn.symm

theorem link_lower (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    M.mate ((Q.lower i h1 (by omega)).dart 3) = (Q.lower (i + 1) (by omega) h2).dart 2 := by
  set U := Q.lower i h1 (by omega)
  set U' := Q.lower (i + 1) (by omega) h2
  have hat : M.atom (M.mate (U.dart 3)) = Q.v (i + 1) := by
    rw [U.neighbor_eq]; rfl
  obtain ⟨j, hj⟩ := FI_cases M hM U' hat
  have hn : M.atom (M.mate (U'.dart j)) = Q.v i := by
    rw [hj, M.mate_mate, U.atom_eq]
  rw [U'.neighbor_eq] at hn
  rw [← hj]
  fin_cases j
  · exfalso; exact hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hn.symm
  · exfalso; exact hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hn.symm
  · rfl
  · exfalso; exact hl.vv_ne (i := i) (j := i + 2) (by omega) (by omega) ⟨h1, by omega⟩ (by omega) hn.symm

/-- the unique dart of `u_i` towards `u_{i+1}` -/
theorem unique_upper (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) {z : D}
    (hz : M.atom z = Q.u i) (hz' : M.atom (M.mate z) = Q.u (i + 1)) :
    z = (Q.upper i h1 (by omega)).dart 3 := by
  set U := Q.upper i h1 (by omega)
  obtain ⟨j, rfl⟩ := FI_cases M hM U hz
  rw [U.neighbor_eq] at hz'
  fin_cases j
  · exfalso; exact hl.uv_ne (i := i + 1) (j := i) (by omega) (by omega) ⟨by omega, h2⟩ hz'.symm
  · exfalso; exact hl.uv_ne (i := i + 1) (j := i) (by omega) (by omega) ⟨by omega, h2⟩ hz'.symm
  · exfalso; exact hl.uu_ne (i := i + 1) (j := i - 1) (by omega) (by omega) ⟨by omega, h2⟩ (by omega) hz'.symm
  · rfl

/-- the unique dart of `v_{i+1}` towards `v_i` -/
theorem unique_lower (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) {z : D}
    (hz : M.atom z = Q.v (i + 1)) (hz' : M.atom (M.mate z) = Q.v i) :
    z = (Q.lower (i + 1) (by omega) h2).dart 2 := by
  set U := Q.lower (i + 1) (by omega) h2
  obtain ⟨j, rfl⟩ := FI_cases M hM U hz
  rw [U.neighbor_eq] at hz'
  fin_cases j
  · exfalso; exact hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hz'.symm
  · exfalso; exact hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ hz'.symm
  · rfl
  · exfalso; exact hl.vv_ne (i := i) (j := i + 1 + 1) (by omega) (by omega) ⟨h1, by omega⟩ (by omega) hz'.symm


omit hM in
theorem dartSign_eq_one_iff (x : D) : M.dartSign x = 1 ↔ M.out x = true := by
  unfold Molecule.dartSign
  cases h : M.out x <;> norm_num

/-- the net outflow of the two rails after rung `i` vanishes along the whole chain -/
theorem flow_zero (hl : Lab M Q φ N)
    (hb : ∀ i, 1 ≤ i → i ≤ k → M.outdeg (Q.u i) = M.indeg (Q.u i) ∧ M.outdeg (Q.v i) = M.indeg (Q.v i))
    (hk : 1 ≤ k)
    (h0 : M.dartSign ((Q.upper 1 le_rfl hk).dart 2) + M.dartSign ((Q.lower 1 le_rfl hk).dart 2) = 0) :
    ∀ i (h1 : 1 ≤ i) (h2 : i ≤ k),
      M.dartSign ((Q.upper i h1 h2).dart 3) + M.dartSign ((Q.lower i h1 h2).dart 3) = 0 := by
  intro i h1 h2
  induction i, h1 using Nat.le_induction with
  | base =>
    have := rail_balance hM hl 1 le_rfl h2 (hb 1 le_rfl h2).1 (hb 1 le_rfl h2).2
    linarith
  | succ i h1 ih =>
    have ih' := ih (by omega)
    have := rail_balance hM hl (i + 1) (by omega) h2 (hb _ (by omega) h2).1 (hb _ (by omega) h2).2
    have e1 := link_upper hM hl i h1 h2
    have e2 := link_lower hM hl i h1 h2
    have s1 := Mole.dartSign_mate M ((Q.upper i h1 (by omega)).dart 3)
    have s2 := Mole.dartSign_mate M ((Q.lower i h1 (by omega)).dart 3)
    rw [e1] at s1
    rw [e2] at s2
    linarith

theorem dir_iff (hl : Lab M Q φ N)
    (hz : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ k),
      M.dartSign ((Q.upper i h1 h2).dart 3) + M.dartSign ((Q.lower i h1 h2).dart 3) = 0)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    M.Directed (Q.u i) (Q.u (i + 1)) ↔ M.Directed (Q.v (i + 1)) (Q.v i) := by
  have hu : M.Directed (Q.u i) (Q.u (i + 1)) ↔ M.out ((Q.upper i h1 (by omega)).dart 3) = true := by
    constructor
    · rintro ⟨x, hx, hx1, hx2⟩
      rw [unique_upper hM hl i h1 h2 hx1 hx2] at hx
      exact hx
    · intro h
      exact ⟨_, h, (Q.upper i h1 (by omega)).atom_eq 3, by rw [(Q.upper i h1 (by omega)).neighbor_eq]; rfl⟩
  have hv : M.Directed (Q.v (i + 1)) (Q.v i) ↔
      M.out ((Q.lower (i + 1) (by omega) h2).dart 2) = true := by
    constructor
    · rintro ⟨x, hx, hx1, hx2⟩
      rw [unique_lower hM hl i h1 h2 hx1 hx2] at hx
      exact hx
    · intro h
      exact ⟨_, h, (Q.lower (i + 1) (by omega) h2).atom_eq 2, by
        rw [(Q.lower (i + 1) (by omega) h2).neighbor_eq]; rfl⟩
  rw [hu, hv, ← dartSign_eq_one_iff, ← dartSign_eq_one_iff]
  have e2 := link_lower hM hl i h1 h2
  have s2 := Mole.dartSign_mate M ((Q.lower i h1 (by omega)).dart 3)
  rw [e2] at s2
  have := hz i h1 (by omega)
  rw [s2]
  constructor <;> intro h <;> linarith


omit hM in
theorem bondsBetween_eq_card_darts (a b : V) (hab : a ≠ b) :
    M.bondsBetween a b = (univ.filter (fun d => M.atom d = a ∧ M.atom (M.mate d) = b)).card := by
  unfold Molecule.bondsBetween Molecule.bonds
  apply Finset.card_bij' (fun x _ => if M.atom x = a then x else M.mate x)
    (fun y _ => if M.out y = true then y else M.mate y)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, Molecule.ends, Sym2.eq_iff] at hx ⊢
    obtain ⟨_, h | h⟩ := hx
    · simp only [h.1, ite_true, true_and]; exact h.2
    · have : M.atom x ≠ a := by rw [h.1]; exact fun e => hab e.symm
      simp only [this, ite_false, M.mate_mate]; exact ⟨h.2, h.1⟩
  · intro y hy
    simp only [mem_filter, mem_univ, true_and, Molecule.ends, Sym2.eq_iff] at hy ⊢
    by_cases ho : M.out y = true
    · simp only [ho, ite_true, true_and]; exact Or.inl hy
    · simp only [ho, Bool.false_eq_true, ite_false]
      refine ⟨?_, Or.inr ⟨hy.2, by rw [M.mate_mate]; exact hy.1⟩⟩
      rw [M.out_mate]; simpa using ho
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    by_cases h : M.atom x = a
    · simp [h, hx.1]
    · have : M.out (M.mate x) = false := by rw [M.out_mate, hx.1]; rfl
      simp [h, this, M.mate_mate]
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    by_cases ho : M.out y = true
    · simp [ho, hy.1]
    · have : M.atom (M.mate y) ≠ a := by rw [hy.2]; exact fun e => hab e.symm
      simp [ho, this, M.mate_mate]

omit hM in
theorem Lab.interior_mem (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k) :
    Q.u i ∈ M.atoms ∧ Q.v i ∈ M.atoms := by
  constructor
  · rw [← (Q.upper i h1 h2).atom_eq 0]; exact M.atom_mem _
  · rw [← (Q.lower i h1 h2).atom_eq 0]; exact M.atom_mem _

theorem rung_bonds (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k) :
    M.bondsBetween (Q.u i) (Q.v i) = 2 := by
  have hc := FI_card_to M hM (Q.upper i h1 h2) (Q.v i)
  rw [bondsBetween_eq_card_darts _ _ (hl.uv_ne (i := i) (j := i) (by omega) (by omega) ⟨h1, h2⟩), hc]
  have : (univ.filter (fun j : Fin 4 => ![Q.v i, Q.v i, Q.u (i - 1), Q.u (i + 1)] j = Q.v i)) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      constructor
      · intro h; exact absurd h.symm (hl.vu_ne (i := i) (j := i - 1) (by omega) (by omega) ⟨h1, h2⟩)
      · intro h; simp at h
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      constructor
      · intro h; exact absurd h.symm (hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, h2⟩)
      · intro h; simp at h
  rw [this]; rfl

theorem rail_bonds_u (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    M.bondsBetween (Q.u i) (Q.u (i + 1)) = 1 := by
  have hc := FI_card_to M hM (Q.upper i h1 (by omega)) (Q.u (i + 1))
  rw [bondsBetween_eq_card_darts _ _ (hl.uu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ (by omega)), hc]
  have : (univ.filter (fun j : Fin 4 => ![Q.v i, Q.v i, Q.u (i - 1), Q.u (i + 1)] j = Q.u (i + 1))) = {3} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      constructor
      · intro h; exact absurd h (hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩)
      · intro h; simp at h
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
      constructor
      · intro h; exact absurd h (hl.vu_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩)
      · intro h; simp at h
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      constructor
      · intro h; exact absurd h.symm (hl.uu_ne (i := i + 1) (j := i - 1) (by omega) (by omega) ⟨by omega, h2⟩ (by omega))
      · intro h; simp at h
    · simp
  rw [this]; rfl

theorem rail_bonds_v (hl : Lab M Q φ N) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ k) :
    M.bondsBetween (Q.v i) (Q.v (i + 1)) = 1 := by
  have hc := FI_card_to M hM (Q.lower i h1 (by omega)) (Q.v (i + 1))
  rw [bondsBetween_eq_card_darts _ _ (hl.vv_ne (i := i) (j := i + 1) (by omega) (by omega) ⟨h1, by omega⟩ (by omega)), hc]
  have : (univ.filter (fun j : Fin 4 => ![Q.u i, Q.u i, Q.v (i - 1), Q.v (i + 1)] j = Q.v (i + 1))) = {3} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      constructor
      · intro h; exact absurd h.symm (hl.vu_ne (i := i + 1) (j := i) (by omega) (by omega) ⟨by omega, h2⟩)
      · intro h; simp at h
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
      constructor
      · intro h; exact absurd h.symm (hl.vu_ne (i := i + 1) (j := i) (by omega) (by omega) ⟨by omega, h2⟩)
      · intro h; simp at h
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      constructor
      · intro h; exact absurd h.symm (hl.vv_ne (i := i + 1) (j := i - 1) (by omega) (by omega) ⟨by omega, h2⟩ (by omega))
      · intro h; simp at h
    · simp
  rw [this]; rfl


/-- The inner chain `u_1..u_k, v_1..v_k` with zero net rail flow is a ladder (for `k = m + 1 ≥ 2`). -/
theorem chain_isLadder {m : ℕ} {Q' : FullRungSequence M (m + 1)} {φ' : V → ℕ} {N' : ℕ}
    (hl : Lab M Q' φ' N') (hm : 1 ≤ m)
    (hz : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ m + 1),
      M.dartSign ((Q'.upper i h1 h2).dart 3) + M.dartSign ((Q'.lower i h1 h2).dart 3) = 0) :
    M.IsLadder (fun j : Fin (m + 1) => Q'.u (j.val + 1)) (fun j : Fin (m + 1) => Q'.v (j.val + 1)) := by
  refine ⟨hm, Q'.distinct, ?_, ?_, ?_⟩
  · intro j
    exact hl.interior_mem (j.val + 1) (by omega) (by omega)
  · intro j
    exact rung_bonds hM hl (j.val + 1) (by omega) (by omega)
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · exact rail_bonds_u hM hl (j.val + 1) (by omega) (by omega)
    · exact rail_bonds_v hM hl (j.val + 1) (by omega) (by omega)
    · exact dir_iff hM hl hz (j.val + 1) (by omega) (by omega)

end WaveTurbulence.VineRho
