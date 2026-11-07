/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Y1c3
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BondErase
import Mathlib.Tactic

/-! # Complete (Y) sequences exist (DH23 L1929)

From a triple bond, a (Y) sequence continues while its (Y2) step creates a new triple bond. In chain terms: the chain
grows while the last pair has two extra single bonds to distinct atoms `c, d` with `c = d` doubly bonded. Take the
longest chain from the triple bond; its ending is (Y1) case 1, 2 or 3, or (Y2) with `c, d` not doubly bonded, i.e. no
new triple bond is created. The extra bonds of the last pair leave the chain, since the earlier pairs are saturated.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace YChain
variable {M : Molecule V D} (C : YChain M)

omit [DecidableEq D] in
/-- A saturated `a i` has all its bonds in the chain, to `nbA i`. -/
theorem mate_mem_nbA_of_lt {i : ℕ} (hi : i < C.n) {z : D} (hz : M.atom z = C.a i) : M.atom (M.mate z) ∈ C.nbA i := by
  classical
  by_contra hno
  have h := card_darts_away (M := M) (C.a i) (C.nbA i) (C.nbA_notMem hi.le)
  rw [C.sum_nbA hi.le, (C.sat i hi).1] at h
  have h0 : ((M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i).card = 0 := by
    split_ifs at h <;> omega
  have hzm : z ∈ (M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, hno⟩
  rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm

omit [DecidableEq D] in
theorem mate_mem_nbB_of_lt {i : ℕ} (hi : i < C.n) {z : D} (hz : M.atom z = C.b i) : M.atom (M.mate z) ∈ C.nbB i := by
  classical
  by_contra hno
  have h := card_darts_away (M := M) (C.b i) (C.nbB i) (C.nbB_notMem hi.le)
  rw [C.sum_nbB hi.le, (C.sat i hi).2] at h
  have h0 : ((M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i).card = 0 := by
    split_ifs at h <;> omega
  have hzm : z ∈ (M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, hno⟩
  rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm

omit [DecidableEq D] in
/-- **An extra bond of `a n` leaves the chain** (no loops). -/
theorem away_a_notMem (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {z : D} (hz : M.atom z = C.a C.n)
    (haway : M.atom (M.mate z) ∉ C.nbA C.n) : M.atom (M.mate z) ∉ C.set := by
  intro hm
  obtain ⟨i, hi, h | h⟩ := C.mem_set.mp hm
  · rcases Nat.lt_or_ge i C.n with hlt | hge
    · have hback := C.mate_mem_nbA_of_lt hlt (z := M.mate z) h
      rw [M.mate_mate, hz] at hback
      rcases Y2End.mem_nbA_iff.mp hback with h' | ⟨_, h'⟩ | ⟨_, h'⟩
      · exact C.ne_ab _ le_rfl i hi h'
      · have := C.inj_a _ le_rfl _ (by omega) h'; omega
      · have := C.inj_a _ le_rfl _ (by omega) h'
        have hn : i = C.n - 1 := by omega
        apply haway
        rw [h, Y2End.mem_nbA_iff]
        right; left; exact ⟨by omega, by rw [hn]⟩
    · have : i = C.n := le_antisymm hi hge
      subst this
      exact hloop z (hz.trans h.symm)
  · rcases Nat.lt_or_ge i C.n with hlt | hge
    · have hback := C.mate_mem_nbB_of_lt hlt (z := M.mate z) h
      rw [M.mate_mate, hz] at hback
      rcases Y2End.mem_nbB_iff.mp hback with h' | ⟨_, h'⟩ | ⟨_, h'⟩
      · have := C.inj_a _ le_rfl i hi h'; omega
      · exact C.ne_ab _ le_rfl _ (by omega) h'
      · exact C.ne_ab _ le_rfl _ (by omega) h'
    · have : i = C.n := le_antisymm hi hge
      subst this
      apply haway
      rw [h, Y2End.mem_nbA_iff]; exact Or.inl rfl

omit [DecidableEq D] in
theorem away_b_notMem (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {z : D} (hz : M.atom z = C.b C.n)
    (haway : M.atom (M.mate z) ∉ C.nbB C.n) : M.atom (M.mate z) ∉ C.set := by
  have h := C.swap.away_a_notMem hloop hz haway
  rwa [C.swap_set] at h

/-- **Extending a chain** by the pair `(c, d)` reached by the two extra bonds of the last pair. -/
def extend (c d : V) (hc : c ∈ M.atoms) (hd : d ∈ M.atoms) (hcY : c ∉ C.set) (hdY : d ∉ C.set) (hcd : c ≠ d)
    (hrung : M.bondsBetween c d = 2) (hra : M.bondsBetween (C.a C.n) c = 1) (hrb : M.bondsBetween (C.b C.n) d = 1)
    (hdeg : M.deg (C.a C.n) = 4 ∧ M.deg (C.b C.n) = 4) : YChain M where
  n := C.n + 1
  a i := if i ≤ C.n then C.a i else c
  b i := if i ≤ C.n then C.b i else d
  inj_a i hi j hj h := by
    by_cases hi' : i ≤ C.n <;> by_cases hj' : j ≤ C.n <;> simp only [hi', hj', ite_true, ite_false] at h
    · exact C.inj_a i hi' j hj' h
    · exact absurd (h ▸ C.a_mem hi') hcY
    · exact absurd (h ▸ C.a_mem hj') hcY
    · omega
  inj_b i hi j hj h := by
    by_cases hi' : i ≤ C.n <;> by_cases hj' : j ≤ C.n <;> simp only [hi', hj', ite_true, ite_false] at h
    · exact C.inj_b i hi' j hj' h
    · exact absurd (h ▸ C.b_mem hi') hdY
    · exact absurd (h ▸ C.b_mem hj') hdY
    · omega
  ne_ab i hi j hj := by
    by_cases hi' : i ≤ C.n <;> by_cases hj' : j ≤ C.n <;> simp only [hi', hj', ite_true, ite_false]
    · exact C.ne_ab i hi' j hj'
    · exact fun h => hdY (h ▸ C.a_mem hi')
    · exact fun h => hcY (h ▸ C.b_mem hj')
    · exact hcd
  mem i hi := by
    by_cases hi' : i ≤ C.n <;> simp only [hi', ite_true, ite_false]
    · exact C.mem i hi'
    · exact ⟨hc, hd⟩
  triple := by simpa using C.triple
  rung i h1 h2 := by
    by_cases hi' : i ≤ C.n <;> simp only [hi', ite_true, ite_false]
    · exact C.rung i h1 hi'
    · exact hrung
  rail i hi := by
    by_cases hi' : i + 1 ≤ C.n
    · simp only [show i ≤ C.n by omega, hi', ite_true]; exact C.rail i (by omega)
    · have : i = C.n := by omega
      subst this
      simp only [le_refl, ite_true, show ¬ C.n + 1 ≤ C.n by omega, ite_false]
      exact ⟨hra, hrb⟩
  sat i hi := by
    by_cases hi' : i < C.n
    · simp only [hi'.le, ite_true]; exact C.sat i hi'
    · have : i = C.n := by omega
      subst this
      simp only [le_refl, ite_true]; exact hdeg

omit [DecidableEq D] in
theorem two_mul_le_card (C : YChain M) : 2 * (C.n + 1) ≤ M.atoms.card := by
  classical
  have h1 : ((range (C.n + 1)).image C.a).card = C.n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact C.inj_a i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h
  have h2 : ((range (C.n + 1)).image C.b).card = C.n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact C.inj_b i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h
  have hdisj : Disjoint ((range (C.n + 1)).image C.a) ((range (C.n + 1)).image C.b) := by
    rw [disjoint_left]
    intro v hv hv'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    obtain ⟨j, hj, h⟩ := mem_image.mp hv'
    exact C.ne_ab i (Nat.lt_succ_iff.mp (mem_range.mp hi)) j (Nat.lt_succ_iff.mp (mem_range.mp hj)) h.symm
  have := card_le_card C.set_sub
  unfold set at this
  rw [card_union_of_disjoint hdisj, h1, h2] at this
  omega

/-- **The ending of a complete (Y) sequence**: (Y1) case 1, 2 or 3, or (Y2) creating no new triple bond. -/
def Complete : Prop :=
  M.deg (C.a C.n) + M.deg (C.b C.n) = 6 ∨ Nonempty (Y1End2 C) ∨ Nonempty (Y1End3 C) ∨
    ∃ E : Y2End C, M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2

end YChain

/-- The one-pair chain at a triple bond. -/
def YChain.start {M : Molecule V D} {a0 b0 : V} (ha0 : a0 ∈ M.atoms) (hb0 : b0 ∈ M.atoms) (hab : a0 ≠ b0)
    (h3 : M.bondsBetween a0 b0 = 3) : YChain M where
  n := 0
  a _ := a0
  b _ := b0
  inj_a i hi j hj _ := by omega
  inj_b i hi j hj _ := by omega
  ne_ab _ _ _ _ := hab
  mem _ _ := ⟨ha0, hb0⟩
  triple := h3
  rung i h1 h2 := by omega
  rail i hi := by omega
  sat i hi := by omega

omit [DecidableEq D] in
/-- **Complete (Y) sequences exist**: from any triple bond, in a loop-free molecule with the in/out caps. -/
theorem exists_complete {M : Molecule V D} (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a0 b0 : V} (ha0 : a0 ∈ M.atoms) (hb0 : b0 ∈ M.atoms)
    (hab : a0 ≠ b0) (h3 : M.bondsBetween a0 b0 = 3) :
    ∃ C : YChain M, C.a 0 = a0 ∧ C.b 0 = b0 ∧ C.Complete := by
  classical
  let Q : ℕ → Prop := fun n => ∃ C : YChain M, C.n = n ∧ C.a 0 = a0 ∧ C.b 0 = b0
  have hex : ∃ n, ¬ Q n := ⟨M.atoms.card, fun ⟨C, hn, _, _⟩ => by have := C.two_mul_le_card; omega⟩
  set N0 := Nat.find hex with hN0
  have hQ0 : Q 0 := ⟨YChain.start ha0 hb0 hab h3, rfl, rfl, rfl⟩
  have hpos : 0 < N0 := Nat.pos_of_ne_zero fun h => (Nat.find_spec hex) (by rw [← hN0, h]; exact hQ0)
  obtain ⟨C, hCn, hCa, hCb⟩ : Q (N0 - 1) := by
    by_contra h
    have := Nat.find_min hex (show N0 - 1 < N0 by omega)
    exact this h
  have hnot : ¬ Q N0 := Nat.find_spec hex
  refine ⟨C, hCa, hCb, ?_⟩
  -- the extra bonds at the last pair
  have hda := C.card_away_last_a
  have hdb := C.card_away_last_b
  have hca := hcap _ (C.mem C.n le_rfl).1
  have hcb := hcap _ (C.mem C.n le_rfl).2
  have h4a := Mole.outdeg_add_indeg M (C.a C.n)
  have h4b := Mole.outdeg_add_indeg M (C.b C.n)
  set Fa := (M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n with hFa
  set Fb := (M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n with hFb
  have hmemFa : ∀ z ∈ Fa, M.atom z = C.a C.n ∧ M.atom (M.mate z) ∉ C.set := fun z hz => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hz
    have h1' := (mem_filter.mp h1).2
    exact ⟨h1', C.away_a_notMem hloop h1' h2⟩
  have hmemFb : ∀ z ∈ Fb, M.atom z = C.b C.n ∧ M.atom (M.mate z) ∉ C.set := fun z hz => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hz
    have h1' := (mem_filter.mp h1).2
    exact ⟨h1', C.away_b_notMem hloop h1' h2⟩
  have hFa1 : Fa.card ≤ 1 := by omega
  have hFb1 : Fb.card ≤ 1 := by omega
  rcases Nat.lt_or_ge Fa.card 1 with ha0' | ha1 <;> rcases Nat.lt_or_ge Fb.card 1 with hb0' | hb1
  · left; omega
  · -- one extra bond, at `b n`
    obtain ⟨y, hy⟩ := card_eq_one.mp (by omega : Fb.card = 1)
    have hym : y ∈ Fb := by rw [hy]; exact mem_singleton_self y
    exact Or.inr (Or.inl ⟨⟨y, Or.inr (hmemFb y hym).1, (hmemFb y hym).2, by omega⟩⟩)
  · obtain ⟨x, hx⟩ := card_eq_one.mp (by omega : Fa.card = 1)
    have hxm : x ∈ Fa := by rw [hx]; exact mem_singleton_self x
    exact Or.inr (Or.inl ⟨⟨x, Or.inl (hmemFa x hxm).1, (hmemFa x hxm).2, by omega⟩⟩)
  · obtain ⟨x, hx⟩ := card_eq_one.mp (by omega : Fa.card = 1)
    obtain ⟨y, hy⟩ := card_eq_one.mp (by omega : Fb.card = 1)
    have hxm : x ∈ Fa := by rw [hx]; exact mem_singleton_self x
    have hym : y ∈ Fb := by rw [hy]; exact mem_singleton_self y
    obtain ⟨hx1, hx2⟩ := hmemFa x hxm
    obtain ⟨hy1, hy2⟩ := hmemFb y hym
    have hdega : M.deg (C.a C.n) = 4 := by omega
    have hdegb : M.deg (C.b C.n) = 4 := by omega
    by_cases hsame : M.atom (M.mate x) = M.atom (M.mate y)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨x, y, hx1, hy1, hx2, hy2, hsame, hdega, hdegb⟩⟩))
    · let E : Y2End C := ⟨x, y, hx1, hy1, hx2, hy2, hsame, hdega, hdegb⟩
      refine Or.inr (Or.inr (Or.inr ⟨E, fun h2 => hnot ?_⟩))
      -- otherwise the chain extends
      have hra : M.bondsBetween (C.a C.n) (M.atom (M.mate x)) = 1 := by
        have hne : C.a C.n ≠ M.atom (M.mate x) := fun h => hx2 (h ▸ C.a_mem le_rfl)
        rw [← Degen.card_neighborDarts M hne]
        refine card_eq_one.mpr ⟨x, eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩⟩
        · exact (Degen.mem_neighborDarts M _ _ x).mpr ⟨hx1, rfl⟩
        · obtain ⟨hz1, hz2⟩ := (Degen.mem_neighborDarts M _ _ z).mp hz
          have : z ∈ Fa := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz1⟩,
            fun h => hx2 (hz2 ▸ C.nbA_sub le_rfl h)⟩
          rw [hx] at this; exact mem_singleton.mp this
      have hrb : M.bondsBetween (C.b C.n) (M.atom (M.mate y)) = 1 := by
        have hne : C.b C.n ≠ M.atom (M.mate y) := fun h => hy2 (h ▸ C.b_mem le_rfl)
        rw [← Degen.card_neighborDarts M hne]
        refine card_eq_one.mpr ⟨y, eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩⟩
        · exact (Degen.mem_neighborDarts M _ _ y).mpr ⟨hy1, rfl⟩
        · obtain ⟨hz1, hz2⟩ := (Degen.mem_neighborDarts M _ _ z).mp hz
          have : z ∈ Fb := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz1⟩,
            fun h => hy2 (hz2 ▸ C.nbB_sub le_rfl h)⟩
          rw [hy] at this; exact mem_singleton.mp this
      refine ⟨C.extend _ _ (M.atom_mem _) (M.atom_mem _) hx2 hy2 hsame h2 hra hrb ⟨hdega, hdegb⟩, ?_, ?_, ?_⟩
      · change C.n + 1 = N0; omega
      · change (if 0 ≤ C.n then C.a 0 else M.atom (M.mate x)) = a0; simp [hCa]
      · change (if 0 ≤ C.n then C.b 0 else M.atom (M.mate y)) = b0; simp [hCb]

end WaveTurbulence.MoleProp4
