/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Route
import Mathlib.Tactic

/-! # Prop 9.6, case (4): a `Q`-route is a ladder `Z_m(Q)`

`zBB m` is the bond function of the ladder with pairs `(false, j), (true, j)`, `j ≤ m`: the rung of pair `j` carries `4`
bonds if `m = 0`, `3` bonds at the two end pairs, `2` bonds otherwise; the rails `(s, j) – (s, j+1)` are single.
`IsZQ N m φ` says `N` is this ladder under the labelling `φ`. A `YRouteQ` of a regular molecule with at most two triple
pairs gives such a labelling (DH23 `ylem1`/(Z) generation; case-4 note Lemma 3.3).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

/-- The bond function of `Z_m(Q)` on the labels `Bool × ℕ`. -/
def zBB (m : ℕ) (x y : Bool × ℕ) : ℕ :=
  if x.2 = y.2 ∧ x.1 ≠ y.1 then (if m = 0 then 4 else if x.2 = 0 ∨ x.2 = m then 3 else 2)
  else if x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2) then 1 else 0

theorem zBB_comm (m : ℕ) (x y : Bool × ℕ) : zBB m x y = zBB m y x := by
  unfold zBB
  by_cases h : x.2 = y.2 ∧ x.1 ≠ y.1
  · have h' : y.2 = x.2 ∧ y.1 ≠ x.1 := ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h, if_pos h']
    simp only [h.1]
  · have h' : ¬ (y.2 = x.2 ∧ y.1 ≠ x.1) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
    rw [if_neg h, if_neg h']
    have : (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ↔ (y.1 = x.1 ∧ (y.2 + 1 = x.2 ∨ x.2 + 1 = y.2)) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
    simp only [this]

section
variable {V : Type u} {D : Type v} {N : Molecule V D} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `N` is the ladder `Z_m(Q)` under the labelling `φ`. -/
structure IsZQ (N : Molecule V D) (m : ℕ) (φ : Bool × ℕ → V) : Prop where
  inj : ∀ x y, x.2 ≤ m → y.2 ≤ m → φ x = φ y → x = y
  atoms : ∀ w, w ∈ N.atoms ↔ ∃ x, x.2 ≤ m ∧ φ x = w
  bb : ∀ x y, x.2 ≤ m → y.2 ≤ m → N.bondsBetween (φ x) (φ y) = zBB m x y

/-- Reversal of the ladder. -/
def zrev (m : ℕ) (φ : Bool × ℕ → V) : Bool × ℕ → V := fun x => φ (x.1, m - x.2)

theorem zBB_rev (m : ℕ) (x y : Bool × ℕ) (hx : x.2 ≤ m) (hy : y.2 ≤ m) :
    zBB m (x.1, m - x.2) (y.1, m - y.2) = zBB m x y := by
  obtain ⟨s, j⟩ := x
  obtain ⟨s', j'⟩ := y
  simp only at hx hy ⊢
  unfold zBB
  simp only
  by_cases hss : s = s'
  · subst hss
    simp only [ne_eq, not_true_eq_false, and_false, if_false, true_and]
    have : (m - j + 1 = m - j' ∨ m - j' + 1 = m - j) ↔ (j + 1 = j' ∨ j' + 1 = j) := by omega
    simp only [this]
  · simp only [hss, ne_eq, not_false_eq_true, and_true, false_and, if_false]
    by_cases hjj : j = j'
    · subst hjj
      simp only [true_and, if_true]
      by_cases hm : m = 0
      · simp [hm]
      · simp only [hm, if_false]
        have : (m - j = 0 ∨ m - j = m) ↔ (j = 0 ∨ j = m) := by omega
        simp only [this]
    · have : ¬ (m - j = m - j') := by omega
      simp [hjj, this]

theorem IsZQ.rev {N : Molecule V D} {m : ℕ} {φ : Bool × ℕ → V} (h : IsZQ N m φ) : IsZQ N m (zrev m φ) where
  inj x y hx hy hxy := by
    have := h.inj (x.1, m - x.2) (y.1, m - y.2) (by simp) (by simp) hxy
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by omega)
  atoms w := by
    rw [h.atoms]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x.1, m - x.2), by simp, by simp [zrev]; congr 1; ext <;> simp; omega⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x.1, m - x.2), by simp, rfl⟩
  bb x y hx hy := by
    unfold zrev
    rw [h.bb _ _ (by simp) (by simp), zBB_rev m x y hx hy]

/-- **Bonds from a chain atom `a i` to the outside**: only the exit `x` of the last pair. -/
theorem bb_a_out {N : Molecule V D} {C : YChain N} (E : Y2End C) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
    {i : ℕ} (hi : i ≤ C.n) {z : V} (hz : z ∉ C.set) :
    N.bondsBetween (C.a i) z = if i = C.n ∧ z = N.atom (N.mate E.x) then 1 else 0 := by
  classical
  have hne : C.a i ≠ z := fun h => hz (h ▸ C.a_mem hi)
  rw [← Degen.card_neighborDarts N hne]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    rw [card_eq_one]
    refine ⟨E.x, ?_⟩
    ext w
    rw [Degen.mem_neighborDarts, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact C.away_last_a_eq (E.deg_a) h1 (h2 ▸ hz) E.hx E.hxo
    · rintro rfl; exact ⟨E.hx, rfl⟩
  · rw [card_eq_zero]
    refine eq_empty_of_forall_notMem fun w hw => ?_
    obtain ⟨h1, h2⟩ := (Degen.mem_neighborDarts N _ _ w).mp hw
    rcases Nat.lt_or_ge i C.n with hlt | hge
    · have := C.mate_mem_nbA_of_lt hlt h1
      exact hz (h2 ▸ C.nbA_sub hlt.le this)
    · have hin : i = C.n := le_antisymm hi hge
      subst hin
      have := C.away_last_a_eq E.deg_a h1 (h2 ▸ hz) E.hx E.hxo
      subst this
      exact hc ⟨rfl, h2.symm⟩

theorem bb_b_out {N : Molecule V D} {C : YChain N} (E : Y2End C) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
    {i : ℕ} (hi : i ≤ C.n) {z : V} (hz : z ∉ C.set) :
    N.bondsBetween (C.b i) z = if i = C.n ∧ z = N.atom (N.mate E.y) then 1 else 0 := by
  classical
  have hne : C.b i ≠ z := fun h => hz (h ▸ C.b_mem hi)
  rw [← Degen.card_neighborDarts N hne]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    rw [card_eq_one]
    refine ⟨E.y, ?_⟩
    ext w
    rw [Degen.mem_neighborDarts, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact C.away_last_b_eq (E.deg_b) h1 (h2 ▸ hz) E.hy E.hyo
    · rintro rfl; exact ⟨E.hy, rfl⟩
  · rw [card_eq_zero]
    refine eq_empty_of_forall_notMem fun w hw => ?_
    obtain ⟨h1, h2⟩ := (Degen.mem_neighborDarts N _ _ w).mp hw
    rcases Nat.lt_or_ge i C.n with hlt | hge
    · have := C.mate_mem_nbB_of_lt hlt h1
      exact hz (h2 ▸ C.nbB_sub hlt.le this)
    · have hin : i = C.n := le_antisymm hi hge
      subst hin
      have := C.away_last_b_eq E.deg_b h1 (h2 ▸ hz) E.hy E.hyo
      subst this
      exact hc ⟨rfl, h2.symm⟩

/-- **Chain-internal bond counts.** -/
theorem bb_aa {N : Molecule V D} {C : YChain N} (E : Y2End C) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
    {i j : ℕ} (hi : i ≤ C.n) (hj : j ≤ C.n) :
    N.bondsBetween (C.a i) (C.a j) = if i + 1 = j ∨ j + 1 = i then 1 else 0 := by
  by_cases h1 : i + 1 = j
  · have := (C.rail i (by omega)).1
    subst h1; simp [this]
  by_cases h2 : j + 1 = i
  · have := (C.rail j (by omega)).1
    subst h2; rw [Degen.bondsBetween_comm]; simp [this]
  rw [if_neg (by omega)]
  by_cases h3 : i = j
  · subst h3; exact bondsBetween_self_eq_zero hloop _
  · exact E.bonds_a_a hi hj (by omega)

theorem bb_bb {N : Molecule V D} {C : YChain N} (E : Y2End C) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
    {i j : ℕ} (hi : i ≤ C.n) (hj : j ≤ C.n) :
    N.bondsBetween (C.b i) (C.b j) = if i + 1 = j ∨ j + 1 = i then 1 else 0 := by
  by_cases h1 : i + 1 = j
  · have := (C.rail i (by omega)).2
    subst h1; simp [this]
  by_cases h2 : j + 1 = i
  · have := (C.rail j (by omega)).2
    subst h2; rw [Degen.bondsBetween_comm]; simp [this]
  rw [if_neg (by omega)]
  by_cases h3 : i = j
  · subst h3; exact bondsBetween_self_eq_zero hloop _
  · exact E.bonds_b_b hi hj (by omega)

theorem bb_ab {N : Molecule V D} {C : YChain N} (E : Y2End C) {i j : ℕ} (hi : i ≤ C.n) (hj : j ≤ C.n) :
    N.bondsBetween (C.a i) (C.b j) = if i = j then (if i = 0 then 3 else 2) else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    split_ifs with h0
    · subst h0; exact C.triple
    · exact C.rung i (by omega) hi
  · rw [if_neg h]; exact E.bonds_a_b hi hj (Ne.symm h)

/-- The chain atom of side `s` (side `su` is the `a`-side) and index `j`. -/
def cat (C : YChain N) (su s : Bool) (j : ℕ) : V := if s = su then C.a j else C.b j

/-- **Bond counts among chain atoms.** -/
theorem bb_cat {N : Molecule V D} {C : YChain N} (E : Y2End C) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z))
    (su s s' : Bool) {j j' : ℕ} (hj : j ≤ C.n) (hj' : j' ≤ C.n) :
    N.bondsBetween (cat C su s j) (cat C su s' j') =
      if j = j' ∧ s ≠ s' then (if j = 0 then 3 else 2)
      else if s = s' ∧ (j + 1 = j' ∨ j' + 1 = j) then 1 else 0 := by
  have haa := bb_aa E hloop hj hj'
  have hbb := bb_bb E hloop hj hj'
  have hab := bb_ab E hj hj'
  have hba : N.bondsBetween (C.b j) (C.a j') = if j' = j then (if j' = 0 then 3 else 2) else 0 := by
    rw [Degen.bondsBetween_comm]; exact bb_ab E hj' hj
  unfold cat
  cases su <;> cases s <;> cases s' <;> simp only [Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false] <;>
    (first | rw [haa] | rw [hbb] | rw [hab] | rw [hba]) <;> simp <;> split_ifs <;> omega

/-- Shift of the ladder by `n + 1` pairs, losing one bond of the first rung. -/
theorem zbb_shift (m n : ℕ) (s s' : Bool) (i i' : ℕ) (hi : i ≤ m) (hi' : i' ≤ m) :
    zBB m (s, i) (s', i') = zBB (m + n + 1) (s, i + n + 1) (s', i' + n + 1) +
      (if i = 0 ∧ i' = 0 ∧ s ≠ s' then 1 else 0) := by
  unfold zBB
  cases s <;> cases s' <;> simp <;> split_ifs <;> omega

/-- Chain atoms against ladder atoms. -/
theorem zbb_chain_ladder (m n j j' : ℕ) (s s' : Bool) (hj : j ≤ n) (hj' : j' ≤ m) :
    zBB (m + n + 1) (s, j) (s', j' + n + 1) = if s = s' ∧ j = n ∧ j' = 0 then 1 else 0 := by
  unfold zBB
  cases s <;> cases s' <;> simp <;> split_ifs <;> omega

theorem zbb_chain_chain (m n j j' : ℕ) (s s' : Bool) (hj : j ≤ n) (hj' : j' ≤ n) :
    zBB (m + n + 1) (s, j) (s', j') =
      if j = j' ∧ s ≠ s' then (if j = 0 then 3 else 2)
      else if s = s' ∧ (j + 1 = j' ∨ j' + 1 = j) then 1 else 0 := by
  unfold zBB
  cases s <;> cases s' <;> simp <;> split_ifs <;> omega

/-- **Base case**: `Q` is `Z_0(Q)`. -/
theorem isZQ_of_isQ {N : Molecule V D} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hQ : IsQ N) :
    ∃ φ, IsZQ N 0 φ := by
  obtain ⟨p, q, hpq, hat, hb, _⟩ := hQ
  refine ⟨fun x => if x.1 then q else p, ?_, ?_, ?_⟩
  · intro x y hx hy h
    obtain ⟨s, j⟩ := x; obtain ⟨s', j'⟩ := y
    simp only at hx hy h
    have : s = s' := by
      cases s <;> cases s' <;> simp_all
    ext <;> simp [this] <;> omega
  · intro w
    rw [hat]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨(false, 0), le_rfl, rfl⟩
      · exact ⟨(true, 0), le_rfl, rfl⟩
    · rintro ⟨⟨s, j⟩, _, rfl⟩
      cases s <;> simp
  · intro x y hx hy
    obtain ⟨s, j⟩ := x; obtain ⟨s', j'⟩ := y
    simp only at hx hy
    have hj : j = 0 := by omega
    have hj' : j' = 0 := by omega
    subst hj hj'
    cases s <;> cases s' <;> simp [zBB]
    · exact bondsBetween_self_eq_zero hloop _
    · exact hb
    · rw [Degen.bondsBetween_comm]; exact hb
    · exact bondsBetween_self_eq_zero hloop _

/-- Bond counts of the post molecule away from the chain. -/
theorem post_bb {N : Molecule V D} {C : YChain N} (E : Y2End C) (hcap : ∀ w ∈ N.atoms, N.outdeg w ≤ 2 ∧ N.indeg w ≤ 2)
    {p q : V} (hp : p ∉ C.set) (hq : q ∉ C.set) :
    (E.toTwoExit hcap).post.bondsBetween p q =
      N.bondsBetween p q + (if s(N.atom (N.mate E.x), N.atom (N.mate E.y)) = s(p, q) then 1 else 0) := by
  have hY : (E.toTwoExit hcap).Y = C.set := E.toTwoExit_Y hcap
  have hpair := toTwoExit_pair E hcap
  change (Mole.addBond (Degen.eraseAtoms N (E.toTwoExit hcap).Y) (E.toTwoExit hcap).d (E.toTwoExit hcap).c).bondsBetween p q = _
  rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq N _ (by rwa [hY]) (by rwa [hY]), hpair]

/-- **The first rung is the pair of exits**: the exits of the chain attach at an end rung of the ladder. -/
theorem end_pair {N : Molecule V D} (hR : RegCore N) {C : YChain N} (E : Y2End C)
    (htrip : (tripSet N).card ≤ 2) {m : ℕ} {φ : Bool × ℕ → V} (hZ : IsZQ (E.toTwoExit hR.cap).post m φ) :
    ∃ (ψ : Bool × ℕ → V) (su : Bool), IsZQ (E.toTwoExit hR.cap).post m ψ ∧ ψ (su, 0) = N.atom (N.mate E.x) ∧
      ψ (!su, 0) = N.atom (N.mate E.y) := by
  classical
  set T := E.toTwoExit hR.cap with hT
  set u := N.atom (N.mate E.x) with hu
  set v := N.atom (N.mate E.y) with hv
  have hY : T.Y = C.set := E.toTwoExit_Y hR.cap
  have hPat : T.post.atoms = N.atoms \ C.set := by rw [T.post_atoms, hY]
  have huC : u ∉ C.set := E.hxo
  have hvC : v ∉ C.set := E.hyo
  have huv : u ≠ v := E.far
  have huP : u ∈ T.post.atoms := by rw [hPat]; exact mem_sdiff.mpr ⟨N.atom_mem _, huC⟩
  have hvP : v ∈ T.post.atoms := by rw [hPat]; exact mem_sdiff.mpr ⟨N.atom_mem _, hvC⟩
  obtain ⟨xu, hxu, hxu'⟩ := (hZ.atoms u).mp huP
  obtain ⟨xv, hxv, hxv'⟩ := (hZ.atoms v).mp hvP
  -- the case `m = 0`
  have key : ∀ ψ : Bool × ℕ → V, IsZQ T.post m ψ → ψ (false, 0) ≠ ψ (true, 0) →
      s(u, v) = s(ψ (false, 0), ψ (true, 0)) → ∃ su, ψ (su, 0) = u ∧ ψ (!su, 0) = v := by
    intro ψ hψ hne h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨false, h1.symm, h2.symm⟩
    · exact ⟨true, h1.symm, h2.symm⟩
  by_cases hm : m = 0
  · subst hm
    have hne : φ (false, 0) ≠ φ (true, 0) := fun h => by
      have := hZ.inj _ _ le_rfl le_rfl h; exact absurd (congrArg Prod.fst this) (by decide)
    refine ⟨φ, xu.1, hZ, ?_, ?_⟩
    · have : xu = (xu.1, 0) := Prod.ext rfl (by omega)
      rw [← this]; exact hxu'
    · have hxv0 : xv = (xv.1, 0) := Prod.ext rfl (by omega)
      have hxu0 : xu = (xu.1, 0) := Prod.ext rfl (by omega)
      have hne' : xv.1 ≠ xu.1 := by
        intro h
        apply huv
        rw [← hxu', ← hxv', hxu0, hxv0, h]
      have : xv.1 = !xu.1 := by
        revert hne'; generalize xv.1 = a; generalize xu.1 = b; cases a <;> cases b <;> simp
      rw [← this, ← hxv0]; exact hxv'
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    -- the end rungs
    have hbb0 : T.post.bondsBetween (φ (false, 0)) (φ (true, 0)) = 3 := by
      rw [hZ.bb _ _ (by simp) (by simp)]; simp [zBB, hm]
    have hbbm : T.post.bondsBetween (φ (false, m)) (φ (true, m)) = 3 := by
      rw [hZ.bb _ _ (by simp) (by simp)]; simp [zBB, hm]
    have a0 : φ (false, 0) ∈ T.post.atoms := (hZ.atoms _).mpr ⟨_, by simp, rfl⟩
    have b0 : φ (true, 0) ∈ T.post.atoms := (hZ.atoms _).mpr ⟨_, by simp, rfl⟩
    have am : φ (false, m) ∈ T.post.atoms := (hZ.atoms _).mpr ⟨_, by simp, rfl⟩
    have bm : φ (true, m) ∈ T.post.atoms := (hZ.atoms _).mpr ⟨_, by simp, rfl⟩
    have hne0 : φ (false, 0) ≠ φ (true, 0) := fun h => by
      have := hZ.inj _ _ (by simp) (by simp) h; simp at this
    have hnem : φ (false, m) ≠ φ (true, m) := fun h => by
      have := hZ.inj _ _ (by simp) (by simp) h; simp at this
    have hR0m : s(φ (false, 0), φ (true, 0)) ≠ s(φ (false, m), φ (true, m)) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this; omega
      · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this
    have hnC : ∀ w ∈ T.post.atoms, w ∉ C.set := fun w hw => by
      rw [hPat] at hw; exact (mem_sdiff.mp hw).2
    -- bond counts in `N`
    have hbN : ∀ p q, p ∈ T.post.atoms → q ∈ T.post.atoms →
        N.bondsBetween p q + (if s(u, v) = s(p, q) then 1 else 0) = T.post.bondsBetween p q := fun p q hp hq =>
      (post_bb E hR.cap (hnC p hp) (hnC q hq)).symm
    have hsub : s(u, v) = s(φ (false, 0), φ (true, 0)) ∨ s(u, v) = s(φ (false, m), φ (true, m)) := by
      by_contra hno
      push Not at hno
      have e0 := hbN _ _ a0 b0
      have em := hbN _ _ am bm
      rw [if_neg hno.1] at e0
      rw [if_neg hno.2] at em
      have t0 : s(φ (false, 0), φ (true, 0)) ∈ tripSet N := tripSet_iff.mpr ⟨_, _, rfl, by omega⟩
      have tm : s(φ (false, m), φ (true, m)) ∈ tripSet N := tripSet_iff.mpr ⟨_, _, rfl, by omega⟩
      have tc : s(C.a 0, C.b 0) ∈ tripSet N :=
        mem_tripSet (C.mem 0 (Nat.zero_le _)).1 (C.mem 0 (Nat.zero_le _)).2 (by rw [C.triple])
      have hc0 : s(C.a 0, C.b 0) ≠ s(φ (false, 0), φ (true, 0)) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hnC _ a0 (h1 ▸ C.a_mem (Nat.zero_le _))
        · exact hnC _ b0 (h1 ▸ C.a_mem (Nat.zero_le _))
      have hcm : s(C.a 0, C.b 0) ≠ s(φ (false, m), φ (true, m)) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hnC _ am (h1 ▸ C.a_mem (Nat.zero_le _))
        · exact hnC _ bm (h1 ▸ C.a_mem (Nat.zero_le _))
      have : ({s(C.a 0, C.b 0), s(φ (false, 0), φ (true, 0)), s(φ (false, m), φ (true, m))} : Finset (Sym2 V)).card = 3 := by
        rw [card_insert_of_notMem (by simp [hc0, hcm]), card_pair hR0m]
      have hsub3 : ({s(C.a 0, C.b 0), s(φ (false, 0), φ (true, 0)), s(φ (false, m), φ (true, m))} : Finset (Sym2 V)) ⊆
          tripSet N := by
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> assumption
      have := card_le_card hsub3
      omega
    rcases hsub with h | h
    · exact ⟨φ, (key φ hZ hne0 h).choose, hZ, (key φ hZ hne0 h).choose_spec.1, (key φ hZ hne0 h).choose_spec.2⟩
    · have hZr := hZ.rev
      have hne0' : zrev m φ (false, 0) ≠ zrev m φ (true, 0) := by
        simpa [zrev] using hnem
      have h' : s(u, v) = s(zrev m φ (false, 0), zrev m φ (true, 0)) := by simpa [zrev] using h
      exact ⟨zrev m φ, (key _ hZr hne0' h').choose, hZr, (key _ hZr hne0' h').choose_spec.1,
        (key _ hZr hne0' h').choose_spec.2⟩

theorem cat_mem (C : YChain N) (su s : Bool) {j : ℕ} (hj : j ≤ C.n) : cat C su s j ∈ C.set := by
  unfold cat; split_ifs
  · exact C.a_mem hj
  · exact C.b_mem hj

theorem cat_inj (C : YChain N) (su s s' : Bool) {j j' : ℕ} (hj : j ≤ C.n) (hj' : j' ≤ C.n)
    (h : cat C su s j = cat C su s' j') : s = s' ∧ j = j' := by
  unfold cat at h
  by_cases hs : s = su <;> by_cases hs' : s' = su
  · rw [if_pos hs, if_pos hs'] at h
    exact ⟨hs.trans hs'.symm, C.inj_a j hj j' hj' h⟩
  · rw [if_pos hs, if_neg hs'] at h
    exact absurd h (C.ne_ab j hj j' hj')
  · rw [if_neg hs, if_pos hs'] at h
    exact absurd h.symm (C.ne_ab j' hj' j hj)
  · rw [if_neg hs, if_neg hs'] at h
    refine ⟨?_, C.inj_b j hj j' hj' h⟩
    revert hs hs'; generalize s = a; generalize s' = b; generalize su = c
    cases a <;> cases b <;> cases c <;> simp

/-- **One (Y2) step preserves the ladder shape** (the (Z) generation, case-4 note Lemma 3.3). -/
theorem zq_step {N : Molecule V D} (hR : RegCore N) {C : YChain N} (E : Y2End C)
    (htrip : (tripSet N).card ≤ 2) {m : ℕ} {φ : Bool × ℕ → V} (hZ : IsZQ (E.toTwoExit hR.cap).post m φ) :
    ∃ m' φ', IsZQ N m' φ' := by
  classical
  obtain ⟨ψ, su, hψ, hψu, hψv⟩ := end_pair hR E htrip hZ
  set T := E.toTwoExit hR.cap with hT
  set n := C.n with hn
  set u := N.atom (N.mate E.x) with hu
  set v := N.atom (N.mate E.y) with hv
  have hY : T.Y = C.set := E.toTwoExit_Y hR.cap
  have hPat : T.post.atoms = N.atoms \ C.set := by rw [T.post_atoms, hY]
  have hψmem : ∀ x : Bool × ℕ, x.2 ≤ m → ψ x ∈ T.post.atoms := fun x hx => (hψ.atoms _).mpr ⟨x, hx, rfl⟩
  have hψnC : ∀ x : Bool × ℕ, x.2 ≤ m → ψ x ∉ C.set := fun x hx => by
    have := hψmem x hx; rw [hPat] at this; exact (mem_sdiff.mp this).2
  have hψu' : ∀ y : Bool × ℕ, y.2 ≤ m → (ψ y = u ↔ y = (su, 0)) := by
    intro y hy
    constructor
    · intro h; exact hψ.inj _ _ hy (by simp) (h.trans hψu.symm)
    · rintro rfl; exact hψu
  have hψv' : ∀ y : Bool × ℕ, y.2 ≤ m → (ψ y = v ↔ y = (!su, 0)) := by
    intro y hy
    constructor
    · intro h; exact hψ.inj _ _ hy (by simp) (h.trans hψv.symm)
    · rintro rfl; exact hψv
  refine ⟨m + n + 1, fun x => if x.2 ≤ n then cat C su x.1 x.2 else ψ (x.1, x.2 - (n + 1)), ?_, ?_, ?_⟩
  · -- injectivity
    intro x y hx hy hxy
    by_cases hxn : x.2 ≤ n <;> by_cases hyn : y.2 ≤ n
    · rw [if_pos hxn, if_pos hyn] at hxy
      obtain ⟨h1, h2⟩ := cat_inj C su _ _ hxn hyn hxy
      exact Prod.ext h1 h2
    · rw [if_pos hxn, if_neg hyn] at hxy
      exact absurd (hxy ▸ cat_mem C su _ hxn) (hψnC _ (by dsimp only; omega))
    · rw [if_neg hxn, if_pos hyn] at hxy
      exact absurd (hxy ▸ cat_mem C su _ hyn) (hψnC _ (by dsimp only; omega))
    · rw [if_neg hxn, if_neg hyn] at hxy
      have := hψ.inj _ _ (by dsimp only; omega) (by dsimp only; omega) hxy
      simp only [Prod.mk.injEq] at this
      exact Prod.ext this.1 (by omega)
  · -- atoms
    intro w
    constructor
    · intro hw
      by_cases hwC : w ∈ C.set
      · obtain ⟨i, hi, h | h⟩ := C.mem_set.mp hwC
        · have hi' : i ≤ n := hi
          exact ⟨(su, i), by dsimp only; omega, by simp [hi', cat, h]⟩
        · have hi' : i ≤ n := hi
          exact ⟨(!su, i), by dsimp only; omega, by simp [hi', cat, h]⟩
      · have hwP : w ∈ T.post.atoms := by rw [hPat]; exact mem_sdiff.mpr ⟨hw, hwC⟩
        obtain ⟨x, hx, rfl⟩ := (hψ.atoms w).mp hwP
        exact ⟨(x.1, x.2 + n + 1), by dsimp only; omega, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hxn : x.2 ≤ n
      · simp only [if_pos hxn]
        exact C.set_sub (cat_mem C su _ hxn)
      · simp only [if_neg hxn]
        have := hψmem (x.1, x.2 - (n + 1)) (by dsimp only; omega)
        rw [hPat] at this; exact (mem_sdiff.mp this).1
  · -- bond counts
    have hbool : ∀ a b : Bool, a ≠ b → (a = su ∧ b = !su) ∨ (a = !su ∧ b = su) := by
      intro a b hab; revert hab; generalize a = a'; generalize b = b'; generalize su = c
      cases a' <;> cases b' <;> cases c <;> simp
    have hnot : ∀ a : Bool, a ≠ su → a = !su := by
      intro a; revert a; generalize su = c; intro a; cases a <;> cases c <;> simp
    have hcl : ∀ x y : Bool × ℕ, x.2 ≤ n → n < y.2 → y.2 ≤ m + n + 1 →
        N.bondsBetween (cat C su x.1 x.2) (ψ (y.1, y.2 - (n + 1))) = zBB (m + n + 1) x y := by
      intro x y hxn hyn1 hym
      have hy' : (y.1, y.2 - (n + 1)).2 ≤ m := by dsimp only; omega
      have hz := hψnC _ hy'
      have hzz := zbb_chain_ladder m n x.2 (y.2 - (n + 1)) x.1 y.1 hxn (by omega)
      have ey : y.2 - (n + 1) + n + 1 = y.2 := by omega
      rw [ey] at hzz
      simp only [Prod.mk.eta] at hzz
      rw [hzz]
      by_cases hs : x.1 = su
      · have h1 : cat C su x.1 x.2 = C.a x.2 := by simp [cat, hs]
        rw [h1, bb_a_out E hR.loop hxn hz]
        have hiff : ψ (y.1, y.2 - (n + 1)) = u ↔ (y.1 = su ∧ y.2 - (n + 1) = 0) := by
          rw [hψu' _ hy']; simp [Prod.ext_iff]
        apply if_congr _ rfl rfl
        rw [hiff, hs, eq_comm (a := su)]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
      · have hs' := hnot _ hs
        have h1 : cat C su x.1 x.2 = C.b x.2 := by simp [cat, hs]
        rw [h1, bb_b_out E hR.loop hxn hz]
        have hiff : ψ (y.1, y.2 - (n + 1)) = v ↔ (y.1 = !su ∧ y.2 - (n + 1) = 0) := by
          rw [hψv' _ hy']; simp [Prod.ext_iff]
        apply if_congr _ rfl rfl
        rw [hiff, hs', eq_comm (a := !su)]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    intro x y hx hy
    by_cases hxn : x.2 ≤ n <;> by_cases hyn : y.2 ≤ n
    · rw [if_pos hxn, if_pos hyn, bb_cat E hR.loop su _ _ hxn hyn, zbb_chain_chain m n _ _ _ _ hxn hyn]
    · rw [if_pos hxn, if_neg hyn]
      exact hcl x y hxn (by omega) hy
    · rw [if_neg hxn, if_pos hyn, Degen.bondsBetween_comm, zBB_comm]
      exact hcl y x hyn (by omega) hx
    · rw [if_neg hxn, if_neg hyn]
      have hx' : (x.1, x.2 - (n + 1)).2 ≤ m := by dsimp only; omega
      have hy' : (y.1, y.2 - (n + 1)).2 ≤ m := by dsimp only; omega
      have e1 := post_bb E hR.cap (hψnC _ hx') (hψnC _ hy')
      have e2 := hψ.bb _ _ hx' hy'
      have e3 := zbb_shift m n x.1 y.1 (x.2 - (n + 1)) (y.2 - (n + 1)) hx' hy'
      have ex : x.2 - (n + 1) + n + 1 = x.2 := by omega
      have ey : y.2 - (n + 1) + n + 1 = y.2 := by omega
      rw [ex, ey] at e3
      simp only [Prod.mk.eta] at e3
      have hind : (s(u, v) = s(ψ (x.1, x.2 - (n + 1)), ψ (y.1, y.2 - (n + 1)))) ↔
          (x.2 - (n + 1) = 0 ∧ y.2 - (n + 1) = 0 ∧ x.1 ≠ y.1) := by
        constructor
        · intro h
          rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have a1 := (hψu' _ hx').mp h1.symm
            have a2 := (hψv' _ hy').mp h2.symm
            simp only [Prod.mk.injEq] at a1 a2
            refine ⟨a1.2, a2.2, ?_⟩
            rw [a1.1, a2.1]; cases su <;> simp
          · have a1 := (hψu' _ hy').mp h1.symm
            have a2 := (hψv' _ hx').mp h2.symm
            simp only [Prod.mk.injEq] at a1 a2
            refine ⟨a2.2, a1.2, ?_⟩
            rw [a1.1, a2.1]; cases su <;> simp
        · rintro ⟨h1, h2, h3⟩
          rcases hbool _ _ h3 with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · rw [← hψu, ← hψv]
            have : (x.1, x.2 - (n + 1)) = (su, 0) := Prod.ext a1 h1
            have : (y.1, y.2 - (n + 1)) = (!su, 0) := Prod.ext a2 h2
            simp_all
          · rw [← hψu, ← hψv, Sym2.eq_swap]
            have : (x.1, x.2 - (n + 1)) = (!su, 0) := Prod.ext a1 h1
            have : (y.1, y.2 - (n + 1)) = (su, 0) := Prod.ext a2 h2
            simp_all
      rw [if_congr hind rfl rfl] at e1
      rw [e2, e3] at e1
      have e1' : N.bondsBetween (ψ (x.1, x.2 - (n + 1))) (ψ (y.1, y.2 - (n + 1))) +
          (if x.2 - (n + 1) = 0 ∧ y.2 - (n + 1) = 0 ∧ x.1 ≠ y.1 then 1 else 0) =
          zBB (m + n + 1) x y + (if x.2 - (n + 1) = 0 ∧ y.2 - (n + 1) = 0 ∧ x.1 ≠ y.1 then 1 else 0) := by
        omega
      omega

end

/-- **A `Q`-route is a ladder `Z_m(Q)`.** -/
theorem yrouteQ_zq : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D},
    YRouteQ N → RegCore N → (tripSet N).card ≤ 2 → ∃ m φ, IsZQ N m φ := by
  intro V D _ _ _ N h
  induction h with
  | done M hQ =>
    intro hR _
    obtain ⟨φ, hφ⟩ := isZQ_of_isQ hR.loop hQ
    exact ⟨0, φ, hφ⟩
  | y2 M hcap C E hcomp _ ih =>
    intro hR htrip
    have hcard := tripSet_post_card E hcap hcomp
    obtain ⟨m, φ, hφ⟩ := ih (hR.post E) (by omega)
    exact zq_step hR E htrip hφ

end WaveTurbulence.FinalCountG8
