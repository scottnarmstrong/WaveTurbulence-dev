/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Ring
import Mathlib.Tactic

/-! # G8-XROUTE: regular molecules with at most four atoms

A nonempty regular molecule without cut vertex on at most four atoms that does not `(Y)`-reduce to `Q`/`T`
is `X` or the quadrilateral of double bonds (`small_final`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem deg_eq_two_atoms {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b : V} (hab : a ≠ b)
    (hs : M.atoms = {a, b}) : M.deg a = M.bondsBetween a b := by
  rw [deg_eq_sum_bb M hloop a, hs]
  have : ({a, b} : Finset V).erase a = {b} := by
    ext z; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨hab.symm, Or.inr rfl⟩
  rw [this, sum_singleton]

theorem deg_eq_three_atoms {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : M.atoms = {a, b, c}) :
    M.deg a = M.bondsBetween a b + M.bondsBetween a c := by
  rw [deg_eq_sum_bb M hloop a, hs]
  have : ({a, b, c} : Finset V).erase a = {b, c} := by
    ext z; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact absurd h2 h1
      · exact Or.inl h2
      · exact Or.inr h2
    · rintro (rfl | rfl)
      · exact ⟨hab.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨hac.symm, Or.inr (Or.inr rfl)⟩
  rw [this, sum_pair hbc]

theorem no_triple_of_atoms {M : Molecule V D} (h : ∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.bondsBetween p q ≠ 3) :
    ∀ p q, M.bondsBetween p q ≠ 3 := by
  intro p q
  by_cases hp : p ∈ M.atoms
  · by_cases hq : q ∈ M.atoms
    · exact h p hp q hq
    · rw [bondsBetween_symm, bb_zero_of_notMem' _ hq]; omega
  · rw [bb_zero_of_notMem' _ hp]; omega

/-- The six ring patterns. -/
def Ring6 (x y z : ℕ) : Prop :=
  (x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 3 ∧ y = 0 ∧ z = 1) ∨ (x = 1 ∧ y = 3 ∧ z = 0) ∨ (x = 0 ∧ y = 3 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = 3) ∨ (x = 0 ∧ y = 1 ∧ z = 3)

/-- The six quadrilateral / `X` patterns. -/
def Pat6 (x y z : ℕ) : Prop :=
  (x = 2 ∧ y = 2 ∧ z = 0) ∨ (x = 2 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 2 ∧ z = 2) ∨ (x = 2 ∧ y = 1 ∧ z = 1) ∨
    (x = 1 ∧ y = 2 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = 2)

theorem nat_cases12 (x y z : ℕ) (h : x + y + z = 4) (hx : x ≤ 3) (hy : y ≤ 3) (hz : z ≤ 3) :
    Ring6 x y z ∨ Pat6 x y z := by
  unfold Ring6 Pat6
  interval_cases x <;> interval_cases y <;> interval_cases z <;> first | (exfalso; omega) | simp

theorem four_eqs {N : Molecule V D} (hR : RegCore N) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hs : N.atoms = {a, b, c, d}) :
    N.bondsBetween a b + N.bondsBetween a c + N.bondsBetween a d = 4 ∧ N.bondsBetween a b ≤ 3 ∧
      N.bondsBetween a c ≤ 3 ∧ N.bondsBetween a d ≤ 3 ∧ N.bondsBetween c d = N.bondsBetween a b ∧
      N.bondsBetween b d = N.bondsBetween a c ∧ N.bondsBetween b c = N.bondsBetween a d := by
  classical
  have sym := bondsBetween_symm N
  have da := deg_eq_three hR.loop hab hac had hbc hbd hcd hs
  have db := deg_eq_three hR.loop (a := b) (b := a) (c := c) (d := d) hab.symm hbc hbd hac had hcd
    (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
  have dc := deg_eq_three hR.loop (a := c) (b := a) (c := b) (d := d) hac.symm hbc.symm hcd hab had hbd
    (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
  have dd := deg_eq_three hR.loop (a := d) (b := a) (c := b) (d := c) had.symm hbd.symm hcd.symm hab hac hbc
    (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
  have ra := hR.reg a (by rw [hs]; simp)
  have rb := hR.reg b (by rw [hs]; simp)
  have rc := hR.reg c (by rw [hs]; simp)
  have rd := hR.reg d (by rw [hs]; simp)
  have s1 := sym b a; have s2 := sym c a; have s3 := sym d a; have s4 := sym c b; have s5 := sym d b
  have s6 := sym d c
  have cut2 : ∀ x y z : V, x ∈ N.atoms → y ∈ N.atoms → z ∈ N.atoms → x ≠ y → z ≠ x → z ≠ y →
      N.bondsBetween x y ≤ 3 := by
    intro x y z hx hy hz hxy hzx hzy
    have h2 := two_le_cross_of_reg N hR.reg hR.conn {x, y}
      (by intro w hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with rfl | rfl <;> assumption) x
      (by simp) z hz (by simp [hzx, hzy])
    have := card_cross_pair N hR.loop hxy
    rw [hR.reg x hx, hR.reg y hy] at this
    omega
  have l1 := cut2 a b c (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp) hab hac.symm hbc.symm
  have l2 := cut2 a c b (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp) hac hab.symm hbc
  have l3 := cut2 a d b (by rw [hs]; simp) (by rw [hs]; simp) (by rw [hs]; simp) had hab.symm hbd
  refine ⟨by omega, l1, l2, l3, by omega, by omega, by omega⟩

theorem small_four_ring {N : Molecule V D} (hR : RegCore N) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hs : N.atoms = {a, b, c, d}) (hnq : ¬ YReachesQT N)
    (q1 : N.bondsBetween c d = N.bondsBetween a b) (q2 : N.bondsBetween b d = N.bondsBetween a c)
    (q3 : N.bondsBetween b c = N.bondsBetween a d)
    (key : Ring6 (N.bondsBetween a b) (N.bondsBetween a c) (N.bondsBetween a d)) : False := by
  classical
  have sym := bondsBetween_symm N
  have s1 := sym b a; have s2 := sym c a; have s3 := sym d a; have s4 := sym c b; have s5 := sym d b
  have s6 := sym d c
  unfold Ring6 at key
  rcases key with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · exact hnq (triple_to_Q hR (p := a) (q := b) (r := c) (t := d) hab hac had hbc hbd hcd hs
      (by omega) (by omega) (by omega) (by omega))
  · exact hnq (triple_to_Q hR (p := a) (q := b) (r := d) (t := c) hab had hac hbd hbc hcd.symm
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
      (by omega) (by omega) (by omega) (by omega))
  · exact hnq (triple_to_Q hR (p := a) (q := c) (r := b) (t := d) hac hab had hbc.symm hcd hbd
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
      (by omega) (by omega) (by omega) (by omega))
  · exact hnq (triple_to_Q hR (p := a) (q := c) (r := d) (t := b) hac had hab hcd hbc.symm hbd.symm
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
      (by omega) (by omega) (by omega) (by omega))
  · exact hnq (triple_to_Q hR (p := a) (q := d) (r := b) (t := c) had hab hac hbd.symm hcd.symm hbc
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
      (by omega) (by omega) (by omega) (by omega))
  · exact hnq (triple_to_Q hR (p := a) (q := d) (r := c) (t := b) had hac hab hcd.symm hbd.symm hbc.symm
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
      (by omega) (by omega) (by omega) (by omega))

theorem small_four_pat {N : Molecule V D} {a b c d : V} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hs : N.atoms = {a, b, c, d})
    (q1 : N.bondsBetween c d = N.bondsBetween a b) (q2 : N.bondsBetween b d = N.bondsBetween a c)
    (q3 : N.bondsBetween b c = N.bondsBetween a d)
    (key : Pat6 (N.bondsBetween a b) (N.bondsBetween a c) (N.bondsBetween a d)) : IsXFinal N := by
  classical
  have sym := bondsBetween_symm N
  have s1 := sym b a; have s2 := sym c a; have s3 := sym d a; have s4 := sym c b; have s5 := sym d b
  have s6 := sym d c
  unfold Pat6 at key
  rcases key with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · refine Or.inr ⟨a, b, d, c, hab, had, hac, hbd, hbc, hcd.symm,
      by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto, ?_⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · refine Or.inr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, ?_⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · refine Or.inr ⟨a, c, b, d, hac, hab, had, hbc.symm, hcd, hbd,
      by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto, ?_⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inl ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, by omega, by omega, by omega, by omega,
      by omega, by omega⟩
  · exact Or.inl ⟨a, c, b, d, hac, hab, had, hbc.symm, hcd, hbd,
      by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto, by omega, by omega, by omega, by omega,
      by omega, by omega⟩
  · exact Or.inl ⟨a, d, b, c, had, hab, hac, hbd.symm, hcd.symm, hbc,
      by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto, by omega, by omega, by omega, by omega,
      by omega, by omega⟩

theorem small_four {N : Molecule V D} (hR : RegCore N) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hs : N.atoms = {a, b, c, d}) (hnq : ¬ YReachesQT N) :
    IsXFinal N := by
  obtain ⟨hsum, l1, l2, l3, q1, q2, q3⟩ := four_eqs hR hab hac had hbc hbd hcd hs
  rcases nat_cases12 _ _ _ hsum l1 l2 l3 with h | h
  · exact (small_four_ring hR hab hac had hbc hbd hcd hs hnq q1 q2 q3 h).elim
  · exact small_four_pat hab hac had hbc hbd hcd hs q1 q2 q3 h

theorem small_final {N : Molecule V D} (hR : RegCore N) (hne : N.atoms.Nonempty) (hc : N.atoms.card ≤ 4)
    (hnq : ¬ YReachesQT N) : IsXFinal N := by
  classical
  have sym := bondsBetween_symm N
  have hself := bondsBetween_self_eq_zero hR.loop
  have hcard : N.atoms.card = 1 ∨ N.atoms.card = 2 ∨ N.atoms.card = 3 ∨ N.atoms.card = 4 := by
    have := card_pos.mpr hne; omega
  rcases hcard with h1 | h2 | h3 | h4
  · exfalso
    obtain ⟨a, ha⟩ := card_eq_one.mp h1
    have := deg_eq_sum_bb N hR.loop a
    rw [ha] at this
    have h4 := hR.reg a (by rw [ha]; simp)
    simp at this
    omega
  · exfalso
    obtain ⟨p, q, hpq, hs⟩ := card_eq_two.mp h2
    have hd := deg_eq_two_atoms hR.loop hpq hs
    have hdp := hR.reg p (by rw [hs]; simp)
    have hdq := hR.reg q (by rw [hs]; simp)
    have hb : N.bondsBetween p q = 4 := by omega
    apply hnq
    refine YReachesQT.done N (no_triple_of_atoms ?_) (Or.inl ⟨p, q, hpq, hs, hb, ?_⟩)
    · intro a ha b hb'
      rw [hs] at ha hb'
      simp only [mem_insert, mem_singleton] at ha hb'
      rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl <;>
        first | (rw [hself]; omega) | omega | (rw [sym]; omega)
    · have := bonds_card_reg hR.reg
      rw [h2] at this
      omega
  · exfalso
    obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := card_eq_three.mp h3
    have dx := deg_eq_three_atoms hR.loop hxy hxz hyz hs
    have dy := deg_eq_three_atoms hR.loop (a := y) (b := x) (c := z) hxy.symm hyz hxz
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
    have dz := deg_eq_three_atoms hR.loop (a := z) (b := x) (c := y) hxz.symm hyz.symm hxy
      (by rw [hs]; ext w; simp only [mem_insert, mem_singleton]; tauto)
    have rx := hR.reg x (by rw [hs]; simp)
    have ry := hR.reg y (by rw [hs]; simp)
    have rz := hR.reg z (by rw [hs]; simp)
    have s1 := sym y x; have s2 := sym z x; have s3 := sym z y
    have e1 : N.bondsBetween x y = 2 := by omega
    have e2 : N.bondsBetween x z = 2 := by omega
    have e3 : N.bondsBetween y z = 2 := by omega
    apply hnq
    refine YReachesQT.done N (no_triple_of_atoms ?_) (Or.inr ⟨x, y, z, hxy, hyz, hxz, hs, e1, e3, e2, ?_⟩)
    · intro a ha b hb'
      rw [hs] at ha hb'
      simp only [mem_insert, mem_singleton] at ha hb'
      rcases ha with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
        first | (rw [hself]; omega) | omega
    · have := bonds_card_reg hR.reg
      rw [h3] at this
      omega
  · -- four atoms
    obtain ⟨a, t, hat, hins, ht3⟩ := card_eq_succ.mp h4
    obtain ⟨b, c, d, hbc, hbd, hcd, ht⟩ := card_eq_three.mp ht3
    have hab : a ≠ b := fun h => hat (by rw [ht, h]; simp)
    have hac : a ≠ c := fun h => hat (by rw [ht, h]; simp)
    have had : a ≠ d := fun h => hat (by rw [ht, h]; simp)
    exact small_four hR hab hac had hbc hbd hcd (by rw [← hins, ht]) hnq

end WaveTurbulence.FinalCountG8
