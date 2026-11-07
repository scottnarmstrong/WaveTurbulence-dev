/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Cells
import Mathlib.Tactic

/-! # The gap of an open cell does not depend on its parametrization

A cell (two double rungs and their two single rails) has its gap `|r|` defined through a parametrization `(u, v)`.
In a molecule with degrees `≤ 4` and no loops, two parametrizations of the same atom set use the same two rail bonds,
unless the "crossed" pairs are single bonds too; then every atom of the cell has its four bonds inside the cell, so no
bond leaves it (a closed group). For an *open* cell (some bond leaves it), all parametrizations give the same `|r|`.
G6's `cell_gap_norm_eq` proves this for molecules (`IsMolecule`); the post molecule of a (Y2) step can be 4-regular,
hence the open-cell form.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Some bond leaves `S`. -/
def OpenSet (M : Molecule V D) (S : Finset V) : Prop := ∃ e : D, M.atom e ∈ S ∧ M.atom (M.mate e) ∉ S

/-- A cell whose gap is well defined: some bond leaves it, or one of its atoms has degree at most three. -/
def GoodCell (M : Molecule V D) (S : Finset V) : Prop := OpenSet M S ∨ ∃ a ∈ S, M.deg a ≤ 3

omit [DecidableEq D] in
/-- If the bonds of `a` to `p, q, r` (distinct, all `≠ a`) add up to four, every bond of `a` goes to `p, q, r`. -/
theorem darts_to_of_full {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {a p q r : V}
    (hdeg : M.deg a ≤ 4) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hsum : 4 ≤ M.bondsBetween a p + M.bondsBetween a q + M.bondsBetween a r) {e : D} (he : M.atom e = a) :
    M.atom (M.mate e) = p ∨ M.atom (M.mate e) = q ∨ M.atom (M.mate e) = r := by
  classical
  by_contra hno
  push Not at hno
  set z := M.atom (M.mate e)
  have hza : a ≠ z := fun h => hloop e (he.trans h)
  have hs := Degen.sum_neighbor_bonds_le_degree M a {p, q, r, z}
    (by simp [hap, haq, har, hza])
  rw [sum_insert (by simp [hpq, hpr, hno.1.symm]), sum_insert (by simp [hqr, hno.2.1.symm]),
    sum_insert (by simp [hno.2.2.symm]), sum_singleton] at hs
  have hz : 1 ≤ M.bondsBetween a z := by
    rw [← Degen.card_neighborDarts M hza]
    exact card_pos.mpr ⟨e, (Degen.mem_neighborDarts M a z e).mpr ⟨he, rfl⟩⟩
  omega

omit [DecidableEq D] in
/-- The rail dart from `a` towards `b` is unique when there is a single bond. -/
theorem dart_unique_of_single {M : Molecule V D} {a b : V} (hab : a ≠ b) (h1 : M.bondsBetween a b = 1)
    {x x' : D} (hx : M.atom x = a ∧ M.atom (M.mate x) = b) (hx' : M.atom x' = a ∧ M.atom (M.mate x') = b) :
    x = x' := by
  have hc := Degen.card_neighborDarts M hab
  rw [h1] at hc
  exact card_le_one.mp hc.le x ((Degen.mem_neighborDarts M a b x).mpr hx) x'
    ((Degen.mem_neighborDarts M a b x').mpr hx')

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem atom_mate_of_ends {M : Molecule V D} {a b : V} (hab : a ≠ b) {x : D} (he : M.ends x = s(a, b))
    (hx : M.atom x = a) : M.atom (M.mate x) = b := by
  have := Sym2.eq_iff.mp he
  rcases this with ⟨_, h⟩ | ⟨h1, _⟩
  · exact h
  · exact absurd (hx.symm.trans h1) hab

omit [DecidableEq D] in
/-- A cell whose crossed pairs are single bonds too is closed. -/
theorem not_open_of_crossed {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4) {u0 u1 v0 v1 : V} (h01 : u0 ≠ u1) (h0v0 : u0 ≠ v0) (h0v1 : u0 ≠ v1)
    (h1v0 : u1 ≠ v0) (h1v1 : u1 ≠ v1) (hvv : v0 ≠ v1)
    (hA : u0 ∈ M.atoms ∧ u1 ∈ M.atoms ∧ v0 ∈ M.atoms ∧ v1 ∈ M.atoms)
    (r0 : M.bondsBetween u0 v0 = 2) (r1 : M.bondsBetween u1 v1 = 2) (su : M.bondsBetween u0 u1 = 1)
    (sv : M.bondsBetween v0 v1 = 1) (c1 : M.bondsBetween u0 v1 = 1) (c2 : M.bondsBetween v0 u1 = 1) :
    ¬ OpenSet M {u0, u1, v0, v1} := by
  rintro ⟨e, he, hout⟩
  have bc := fun a b => Degen.bondsBetween_comm M a b
  simp only [mem_insert, mem_singleton, not_or] at he hout
  obtain ⟨o1, o2, o3, o4⟩ := hout
  rcases he with h | h | h | h
  · rcases darts_to_of_full hloop (hdeg _ hA.1) (p := v0) (q := u1) (r := v1) (Ne.symm h1v0) hvv h1v1
      h0v0 h01 h0v1 (by rw [r0, su, c1]) h with h' | h' | h'
    exacts [o3 h', o2 h', o4 h']
  · rcases darts_to_of_full hloop (hdeg _ hA.2.1) (p := v1) (q := u0) (r := v0) (Ne.symm h0v1) (Ne.symm hvv)
      h0v0 h1v1 (Ne.symm h01) h1v0 (by rw [r1, bc u1 u0, su, bc u1 v0, c2]) h with h' | h' | h'
    exacts [o4 h', o1 h', o3 h']
  · rcases darts_to_of_full hloop (hdeg _ hA.2.2.1) (p := u0) (q := v1) (r := u1) h0v1 h01 (Ne.symm h1v1)
      (Ne.symm h0v0) hvv (Ne.symm h1v0) (by rw [bc v0 u0, r0, sv, c2]) h with h' | h' | h'
    exacts [o1 h', o4 h', o2 h']
  · rcases darts_to_of_full hloop (hdeg _ hA.2.2.2) (p := u1) (q := v0) (r := u0) h1v0 (Ne.symm h01)
      (Ne.symm h0v0) (Ne.symm h1v1) (Ne.symm hvv) (Ne.symm h0v1)
      (by rw [bc v1 u1, r1, bc v1 v0, sv, bc v1 u0, c1]) h with h' | h' | h'
    exacts [o2 h', o3 h', o1 h']

omit [DecidableEq D] in

/-- With crossed rails every atom of the cell has four bonds inside it. -/
theorem four_le_deg_of_crossed {M : Molecule V D} {u0 u1 v0 v1 : V} (h01 : u0 ≠ u1) (h0v0 : u0 ≠ v0)
    (h0v1 : u0 ≠ v1) (h1v0 : u1 ≠ v0) (h1v1 : u1 ≠ v1) (hvv : v0 ≠ v1)
    (r0 : M.bondsBetween u0 v0 = 2) (r1 : M.bondsBetween u1 v1 = 2) (su : M.bondsBetween u0 u1 = 1)
    (sv : M.bondsBetween v0 v1 = 1) (c1 : M.bondsBetween u0 v1 = 1) (c2 : M.bondsBetween v0 u1 = 1) :
    ∀ a ∈ ({u0, u1, v0, v1} : Finset V), 4 ≤ M.deg a := by
  have bc := fun a b => Degen.bondsBetween_comm M a b
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · have h := Degen.sum_neighbor_bonds_le_degree M a {v0, u1, v1} (by simp [h0v0, h01, h0v1])
    rw [sum_insert (by simp [Ne.symm h1v0, hvv]), sum_insert (by simp [h1v1]), sum_singleton, r0, su, c1] at h
    omega
  · have h := Degen.sum_neighbor_bonds_le_degree M a {v1, u0, v0} (by simp [h1v1, Ne.symm h01, h1v0])
    rw [sum_insert (by simp [Ne.symm h0v1, Ne.symm hvv]), sum_insert (by simp [h0v0]), sum_singleton, r1,
      bc a u0, su, bc a v0, c2] at h
    omega
  · have h := Degen.sum_neighbor_bonds_le_degree M a {u0, v1, u1} (by simp [Ne.symm h0v0, hvv, Ne.symm h1v0])
    rw [sum_insert (by simp [h0v1, h01]), sum_insert (by simp [Ne.symm h1v1]), sum_singleton, bc a u0, r0, sv, c2]
      at h
    omega
  · have h := Degen.sum_neighbor_bonds_le_degree M a {u1, v0, u0} (by simp [Ne.symm h1v1, Ne.symm hvv, Ne.symm h0v1])
    rw [sum_insert (by simp [h1v0, Ne.symm h01]), sum_insert (by simp [Ne.symm h0v0]), sum_singleton, bc a u1, r1,
      bc a v0, sv, bc a u0, c1] at h
    omega

omit [DecidableEq D] in
/-- Two darts of the same single bond carry the same vector. -/
theorem kvec_eq_of_single {M : Molecule V D} {d : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) {a b : V} (hab : a ≠ b) (h1 : M.bondsBetween a b = 1) {z z' : D}
    (hz : M.ends z = s(a, b)) (hz' : M.ends z' = s(a, b)) : Molecule.kvec L w κ z = Molecule.kvec L w κ z' := by
  have norm_dart : ∀ t : D, M.ends t = s(a, b) → ∃ t₀, (M.atom t₀ = a ∧ M.atom (M.mate t₀) = b) ∧
      Molecule.kvec L w κ t = Molecule.kvec L w κ t₀ := by
    intro t ht
    rcases Sym2.eq_iff.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t, ⟨h1, h2⟩, rfl⟩
    · exact ⟨M.mate t, ⟨h2, by rw [M.mate_mate]; exact h1⟩, by simp [Molecule.kvec, hb]⟩
  obtain ⟨t₀, ht₀, hk⟩ := norm_dart z hz
  obtain ⟨t₀', ht₀', hk'⟩ := norm_dart z' hz'
  rw [hk, hk', dart_unique_of_single hab h1 ht₀ ht₀']

omit [DecidableEq D] in
/-- **Good cells (open, or with an atom of degree `≤ 3`) have a well-defined gap norm.** -/
theorem cell_gap_norm_eq_of_good {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4) {d : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) {u v p q : Fin 2 → V} (hL : Degen.SourceLadder M u v)
    (hL' : Degen.SourceLadder M p q) (hS : Molecule.ladderAtoms p q = Molecule.ladderAtoms u v)
    (hgood : GoodCell M (Molecule.ladderAtoms u v)) {r s : Mom d} (hr : M.IsLadderGap L w κ u v hL.1 r)
    (hs : M.IsLadderGap L w κ p q hL'.1 s) : ‖r‖ = ‖s‖ := by
  obtain ⟨x, y, hxe, hye, _, _, rfl⟩ := hr
  obtain ⟨x', y', hxe', hye', _, _, rfl⟩ := hs
  obtain ⟨_, hinj, hmem, hrung, hrail⟩ := hL
  obtain ⟨_, hinj', _, hrung', hrail'⟩ := hL'
  obtain ⟨su, sv, _⟩ := hrail 0
  obtain ⟨sp, sq, _⟩ := hrail' 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at su sv sp sq
  have r0 := hrung 0
  have r1 := hrung 1
  have rp0 := hrung' 0
  have rp1 := hrung' 1
  change M.ends x = s(u 0, u 1) at hxe
  change M.ends y = s(v 0, v 1) at hye
  change M.ends x' = s(p 0, p 1) at hxe'
  change M.ends y' = s(q 0, q 1) at hye'
  have ne : ∀ {a b : Fin 2 ⊕ Fin 2}, a ≠ b → Sum.elim u v a ≠ Sum.elim u v b := fun h e => h (hinj e)
  have ne' : ∀ {a b : Fin 2 ⊕ Fin 2}, a ≠ b → Sum.elim p q a ≠ Sum.elim p q b := fun h e => h (hinj' e)
  have h01 : u 0 ≠ u 1 := ne (a := .inl 0) (b := .inl 1) (by decide)
  have h0v0 : u 0 ≠ v 0 := ne (a := .inl 0) (b := .inr 0) (by decide)
  have h0v1 : u 0 ≠ v 1 := ne (a := .inl 0) (b := .inr 1) (by decide)
  have h1v0 : u 1 ≠ v 0 := ne (a := .inl 1) (b := .inr 0) (by decide)
  have h1v1 : u 1 ≠ v 1 := ne (a := .inl 1) (b := .inr 1) (by decide)
  have hvv : v 0 ≠ v 1 := ne (a := .inr 0) (b := .inr 1) (by decide)
  have hp10 : p 1 ≠ p 0 := ne' (a := .inl 1) (b := .inl 0) (by decide)
  have hp1q0 : p 1 ≠ q 0 := ne' (a := .inl 1) (b := .inr 0) (by decide)
  have hSet : Molecule.ladderAtoms u v = {u 0, u 1, v 0, v 1} := by
    ext z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  have hpS : ∀ i, p i ∈ ({u 0, u 1, v 0, v 1} : Finset V) := fun i => by
    rw [← hSet, ← hS]; exact mem_union_left _ (mem_image_of_mem _ (mem_univ i))
  have hA : u 0 ∈ M.atoms ∧ u 1 ∈ M.atoms ∧ v 0 ∈ M.atoms ∧ v 1 ∈ M.atoms :=
    ⟨(hmem 0).1, (hmem 1).1, (hmem 0).2, (hmem 1).2⟩
  have bc := fun a b => Degen.bondsBetween_comm M a b
  have crossed : M.bondsBetween (u 0) (v 1) = 1 → M.bondsBetween (v 0) (u 1) = 1 → False := fun c1 c2 => by
    rw [hSet] at hgood
    rcases hgood with hopen | ⟨a, ha, hle⟩
    · exact not_open_of_crossed hloop hdeg h01 h0v0 h0v1 h1v0 h1v1 hvv hA r0 r1 su sv c1 c2 hopen
    · have := four_le_deg_of_crossed h01 h0v0 h0v1 h1v0 h1v1 hvv r0 r1 su sv c1 c2 a ha
      omega
  have pu : ∀ {a a' b : V}, a ∈ M.atoms → M.bondsBetween a a' = 2 → M.bondsBetween a b = 1 →
      ∀ {c : V}, M.bondsBetween a c = 2 → c = a' := fun ha h2 h1 _ hc =>
    double_partner_unique hloop (hdeg _ ha) h2 h1 hc
  -- the rail bonds of `(p, q)` are those of `(u, v)`, possibly exchanged
  have hp0 := hpS 0
  have hp1 := hpS 1
  simp only [mem_insert, mem_singleton] at hp0 hp1
  generalize p 0 = P0 at rp0 sp hp10 hxe' hp0
  generalize p 1 = P1 at rp1 sp hp10 hp1q0 hxe' hp1
  generalize q 0 = Q0 at rp0 sq hp1q0 hye'
  generalize q 1 = Q1 at rp1 sq hye'
  have key : (s(P0, P1) = s(u 0, u 1) ∧ s(Q0, Q1) = s(v 0, v 1)) ∨
      (s(P0, P1) = s(v 0, v 1) ∧ s(Q0, Q1) = s(u 0, u 1)) := by
    rcases hp0 with rfl | rfl | rfl | rfl
    · obtain rfl := pu hA.1 r0 su rp0
      rcases hp1 with rfl | rfl | rfl | rfl
      · exact absurd rfl hp10
      · obtain rfl := pu hA.2.1 r1 (by rw [bc]; exact su) rp1
        exact Or.inl ⟨rfl, rfl⟩
      · exact absurd rfl hp1q0
      · obtain rfl := pu hA.2.2.2 (by rw [bc]; exact r1) (by rw [bc]; exact sv) rp1
        exact (crossed sp sq).elim
    · obtain rfl := pu hA.2.1 r1 (by rw [bc]; exact su) rp0
      rcases hp1 with rfl | rfl | rfl | rfl
      · obtain rfl := pu hA.1 r0 su rp1
        exact Or.inl ⟨Sym2.eq_swap, Sym2.eq_swap⟩
      · exact absurd rfl hp10
      · obtain rfl := pu hA.2.2.1 (by rw [bc]; exact r0) sv rp1
        exact (crossed (by rw [bc]; exact sq) (by rw [bc]; exact sp)).elim
      · exact absurd rfl hp1q0
    · obtain rfl := pu hA.2.2.1 (by rw [bc]; exact r0) sv rp0
      rcases hp1 with rfl | rfl | rfl | rfl
      · exact absurd rfl hp1q0
      · obtain rfl := pu hA.2.1 r1 (by rw [bc]; exact su) rp1
        exact (crossed sq sp).elim
      · exact absurd rfl hp10
      · obtain rfl := pu hA.2.2.2 (by rw [bc]; exact r1) (by rw [bc]; exact sv) rp1
        exact Or.inr ⟨rfl, rfl⟩
    · obtain rfl := pu hA.2.2.2 (by rw [bc]; exact r1) (by rw [bc]; exact sv) rp0
      rcases hp1 with rfl | rfl | rfl | rfl
      · obtain rfl := pu hA.1 r0 su rp1
        exact (crossed (by rw [bc]; exact sp) (by rw [bc]; exact sq)).elim
      · exact absurd rfl hp1q0
      · obtain rfl := pu hA.2.2.1 (by rw [bc]; exact r0) sv rp1
        exact Or.inr ⟨Sym2.eq_swap, Sym2.eq_swap⟩
      · exact absurd rfl hp10
  unfold Molecule.gapAt
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rw [kvec_eq_of_single hb h01 su (hxe'.trans k1) hxe, kvec_eq_of_single hb hvv sv (hye'.trans k2) hye]
  · rw [kvec_eq_of_single hb hvv sv (hxe'.trans k1) hye, kvec_eq_of_single hb h01 su (hye'.trans k2) hxe,
      norm_sub_rev]

end WaveTurbulence.MoleProp4
