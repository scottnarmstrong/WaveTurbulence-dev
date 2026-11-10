/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YEnd
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeNormalization
import Mathlib.Tactic

/-! # Removing one bond; neighbours of chain atoms; the mirror chain

* Bond counts and degrees of `𝕄 ∖ {ℓ}` (G6 `MoleProp.eraseBond`).
* In a (Y2)-ended chain, a dart from `a i` into the chain ends in `nbA i` (degree count), so all other bond counts
  inside the chain vanish.
* Exchanging the roles of `a` and `b` gives again a (Y) chain with a (Y2) ending, with the same atoms.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

section EraseBond
variable (M : Molecule V D) (e : D)

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem ends_mate (z : D) : M.ends (M.mate z) = M.ends z := by
  unfold Molecule.ends; rw [M.mate_mate]; exact Sym2.eq_swap

/-- **Bond counts after removing the bond of `e`.** -/
theorem bondsBetween_eraseBond_add (p q : V) :
    (MoleProp.eraseBond M e).bondsBetween p q + (if M.ends e = s(p, q) then 1 else 0) = M.bondsBetween p q := by
  classical
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter, filter_filter]
  set S := univ.filter fun x : D => M.out x = true ∧ M.ends x = s(p, q)
  have hsplit := card_filter_add_card_filter_not (s := S) (p := fun x => x ≠ e ∧ x ≠ M.mate e)
  have h1 : (univ.filter fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} =>
      (MoleProp.eraseBond M e).out x = true ∧ (MoleProp.eraseBond M e).ends x = s(p, q)).card =
      (S.filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
    refine card_bij (fun x _ => x.val) ?_ (fun x _ y _ h => Subtype.ext h) ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and, S] at hx ⊢
      exact ⟨hx, x.property⟩
    · intro x hx
      simp only [mem_filter, mem_univ, true_and, S] at hx
      exact ⟨⟨x, hx.2⟩, by simp only [mem_filter, mem_univ, true_and]; exact hx.1, rfl⟩
  have h2 : (S.filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)).card = if M.ends e = s(p, q) then 1 else 0 := by
    have hne : e ≠ M.mate e := fun h => M.mate_ne e h.symm
    have hset : (S.filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)) =
        ({e, M.mate e} : Finset D).filter fun x => M.out x = true ∧ M.ends x = s(p, q) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, S, mem_insert, mem_singleton, not_and_or, not_not]
      tauto
    rw [hset, filter_insert, filter_singleton, ends_mate, M.out_mate]
    by_cases ho : M.out e = true <;> by_cases he : M.ends e = s(p, q) <;> simp [ho, he]
  rw [h1, ← h2]
  exact hsplit

/-- **Degrees after removing the bond of `e`.** -/
theorem deg_eraseBond_add (v : V) :
    (MoleProp.eraseBond M e).deg v + (if M.atom e = v then 1 else 0) + (if M.atom (M.mate e) = v then 1 else 0) =
      M.deg v := by
  classical
  unfold Molecule.deg Molecule.dartsAt
  have hsplit := card_filter_add_card_filter_not (s := univ.filter fun x : D => M.atom x = v)
    (p := fun x => x ≠ e ∧ x ≠ M.mate e)
  have h1 : (univ.filter fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => (MoleProp.eraseBond M e).atom x = v).card =
      ((univ.filter fun x : D => M.atom x = v).filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
    refine card_bij (fun x _ => x.val) ?_ (fun x _ y _ h => Subtype.ext h) ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨hx, x.property⟩
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      exact ⟨⟨x, hx.2⟩, by simp only [mem_filter, mem_univ, true_and]; exact hx.1, rfl⟩
  have hne : e ≠ M.mate e := fun h => M.mate_ne e h.symm
  have h2 : ((univ.filter fun x : D => M.atom x = v).filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)).card =
      (if M.atom e = v then 1 else 0) + (if M.atom (M.mate e) = v then 1 else 0) := by
    have hset : ((univ.filter fun x : D => M.atom x = v).filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)) =
        ({e, M.mate e} : Finset D).filter fun x => M.atom x = v := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, not_and_or, not_not]
      tauto
    rw [hset, filter_insert, filter_singleton]
    by_cases ha : M.atom e = v <;> by_cases hb : M.atom (M.mate e) = v <;> simp [ha, hb, hne]
  change (univ.filter fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => (MoleProp.eraseBond M e).atom x = v).card + _ + _ = _
  rw [h1, add_assoc, ← h2]
  exact hsplit

theorem bondsBetween_eraseBond_of_ne {p q : V} (h : M.ends e ≠ s(p, q)) :
    (MoleProp.eraseBond M e).bondsBetween p q = M.bondsBetween p q := by
  have := bondsBetween_eraseBond_add M e p q
  simp only [h, ite_false, add_zero] at this
  exact this

theorem deg_eraseBond_of_ne {v : V} (h1 : M.atom e ≠ v) (h2 : M.atom (M.mate e) ≠ v) :
    (MoleProp.eraseBond M e).deg v = M.deg v := by
  have := deg_eraseBond_add M e v
  simp only [h1, h2, ite_false, add_zero] at this
  exact this

theorem bondsBetween_eraseBond_le' (p q : V) : (MoleProp.eraseBond M e).bondsBetween p q ≤ M.bondsBetween p q := by
  have := bondsBetween_eraseBond_add M e p q
  omega

end EraseBond

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

include E in
omit [DecidableEq D] in
/-- **A dart from `a i` into the chain ends in `nbA i`.** -/
theorem mate_mem_nbA {i : ℕ} (hi : i ≤ C.n) {z : D} (hz : M.atom z = C.a i) (hm : M.atom (M.mate z) ∈ C.set) :
    M.atom (M.mate z) ∈ C.nbA i := by
  classical
  by_contra hno
  have h := YChain.card_darts_away (M := M) (C.a i) (C.nbA i) (C.nbA_notMem hi)
  rw [C.sum_nbA hi, E.deg_four _ (C.a_mem hi)] at h
  have hzm : z ∈ (M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, hno⟩
  rcases Nat.lt_or_ge i C.n with hlt | hge
  · have h0 : ((M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i).card = 0 := by
      split_ifs at h <;> omega
    rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm
  · have hin : i = C.n := le_antisymm hi hge
    subst hin
    have hxm : E.x ∈ (M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, E.hx⟩, fun h' => E.hxo (C.nbA_sub le_rfl h')⟩
    have h1 : ((M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n).card ≤ 1 := by
      split_ifs at h <;> omega
    have := card_le_one.mp h1 z hzm E.x hxm
    subst this
    exact E.hxo hm

include E in
omit [DecidableEq D] in
/-- A dart from `b i` into the chain ends in `nbB i`. -/
theorem mate_mem_nbB {i : ℕ} (hi : i ≤ C.n) {z : D} (hz : M.atom z = C.b i) (hm : M.atom (M.mate z) ∈ C.set) :
    M.atom (M.mate z) ∈ C.nbB i := by
  classical
  by_contra hno
  have h := YChain.card_darts_away (M := M) (C.b i) (C.nbB i) (C.nbB_notMem hi)
  rw [C.sum_nbB hi, E.deg_four _ (C.b_mem hi)] at h
  have hzm : z ∈ (M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, hno⟩
  rcases Nat.lt_or_ge i C.n with hlt | hge
  · have h0 : ((M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i).card = 0 := by
      split_ifs at h <;> omega
    rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm
  · have hin : i = C.n := le_antisymm hi hge
    subst hin
    have hym : E.y ∈ (M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, E.hy⟩, fun h' => E.hyo (C.nbB_sub le_rfl h')⟩
    have h1 : ((M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n).card ≤ 1 := by
      split_ifs at h <;> omega
    have := card_le_one.mp h1 z hzm E.y hym
    subst this
    exact E.hyo hm

include E in
omit [DecidableEq D] in
/-- No bond from `a i` to a chain atom outside `nbA i`. -/
theorem bonds_a_eq_zero {i : ℕ} (hi : i ≤ C.n) {w : V} (hw : w ∈ C.set) (hwn : w ∉ C.nbA i) (hne : C.a i ≠ w) :
    M.bondsBetween (C.a i) w = 0 := by
  rw [← Degen.card_neighborDarts M hne, card_eq_zero]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨h1, h2⟩ := (Degen.mem_neighborDarts M _ _ z).mp hz
  exact hwn (h2 ▸ E.mate_mem_nbA hi h1 (h2 ▸ hw))

include E in
omit [DecidableEq D] in
/-- No bond from `b i` to a chain atom outside `nbB i`. -/
theorem bonds_b_eq_zero {i : ℕ} (hi : i ≤ C.n) {w : V} (hw : w ∈ C.set) (hwn : w ∉ C.nbB i) (hne : C.b i ≠ w) :
    M.bondsBetween (C.b i) w = 0 := by
  rw [← Degen.card_neighborDarts M hne, card_eq_zero]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨h1, h2⟩ := (Degen.mem_neighborDarts M _ _ z).mp hz
  exact hwn (h2 ▸ E.mate_mem_nbB hi h1 (h2 ▸ hw))

omit [DecidableEq D] in
/-- Membership in `nbA i`. -/
theorem mem_nbA_iff {i : ℕ} {w : V} :
    w ∈ C.nbA i ↔ w = C.b i ∨ (0 < i ∧ w = C.a (i - 1)) ∨ (i < C.n ∧ w = C.a (i + 1)) := by
  simp only [YChain.nbA, mem_insert, mem_union]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · split_ifs at h with h0
      · exact Or.inr (Or.inl ⟨h0, mem_singleton.mp h⟩)
      · simp at h
    · split_ifs at h with h0
      · exact Or.inr (Or.inr ⟨h0, mem_singleton.mp h⟩)
      · simp at h
  · rintro (h | ⟨h0, h⟩ | ⟨h0, h⟩)
    · exact Or.inl h
    · right; left; simp [h0, h]
    · right; right; simp [h0, h]

omit [DecidableEq D] in
theorem mem_nbB_iff {i : ℕ} {w : V} :
    w ∈ C.nbB i ↔ w = C.a i ∨ (0 < i ∧ w = C.b (i - 1)) ∨ (i < C.n ∧ w = C.b (i + 1)) := by
  simp only [YChain.nbB, mem_insert, mem_union]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · split_ifs at h with h0
      · exact Or.inr (Or.inl ⟨h0, mem_singleton.mp h⟩)
      · simp at h
    · split_ifs at h with h0
      · exact Or.inr (Or.inr ⟨h0, mem_singleton.mp h⟩)
      · simp at h
  · rintro (h | ⟨h0, h⟩ | ⟨h0, h⟩)
    · exact Or.inl h
    · right; left; simp [h0, h]
    · right; right; simp [h0, h]

include E in
omit [DecidableEq D] in
/-- `a i` and `b k` with `k ≠ i` are not bonded; nor are `a i`, `a k` with `|i - k| ≥ 2`. -/
theorem bonds_a_b {i k : ℕ} (hi : i ≤ C.n) (hk : k ≤ C.n) (hik : k ≠ i) : M.bondsBetween (C.a i) (C.b k) = 0 := by
  classical
  refine E.bonds_a_eq_zero hi (C.b_mem hk) ?_ (C.ne_ab i hi k hk)
  rw [Y2End.mem_nbA_iff]
  rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
  · exact hik (C.inj_b k hk i hi h)
  · exact C.ne_ab _ (by omega) k hk h.symm
  · exact C.ne_ab _ (by omega) k hk h.symm

include E in
omit [DecidableEq D] in
theorem bonds_a_a {i k : ℕ} (hi : i ≤ C.n) (hk : k ≤ C.n) (hik : k + 1 < i ∨ i + 1 < k) :
    M.bondsBetween (C.a i) (C.a k) = 0 := by
  classical
  refine E.bonds_a_eq_zero hi (C.a_mem hk) ?_ (fun h => by have := C.inj_a i hi k hk h; omega)
  rw [Y2End.mem_nbA_iff]
  rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
  · exact C.ne_ab k hk i hi h
  · have := C.inj_a k hk _ (by omega) h; omega
  · have := C.inj_a k hk _ (by omega) h; omega

include E in
omit [DecidableEq D] in
theorem bonds_b_b {i k : ℕ} (hi : i ≤ C.n) (hk : k ≤ C.n) (hik : k + 1 < i ∨ i + 1 < k) :
    M.bondsBetween (C.b i) (C.b k) = 0 := by
  classical
  refine E.bonds_b_eq_zero hi (C.b_mem hk) ?_ (fun h => by have := C.inj_b i hi k hk h; omega)
  rw [Y2End.mem_nbB_iff]
  rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
  · exact C.ne_ab i hi k hk h.symm
  · have := C.inj_b k hk _ (by omega) h; omega
  · have := C.inj_b k hk _ (by omega) h; omega

end Y2End

namespace YChain
variable {M : Molecule V D} (C : YChain M)

/-- **The mirror chain**: exchange `a` and `b`. -/
def swap : YChain M where
  n := C.n
  a := C.b
  b := C.a
  inj_a := C.inj_b
  inj_b := C.inj_a
  ne_ab i hi j hj h := C.ne_ab j hj i hi h.symm
  mem i hi := (C.mem i hi).symm
  triple := by rw [Degen.bondsBetween_comm]; exact C.triple
  rung i h1 h2 := by rw [Degen.bondsBetween_comm]; exact C.rung i h1 h2
  rail i hi := (C.rail i hi).symm
  sat i hi := (C.sat i hi).symm

omit [DecidableEq D] in
theorem swap_set : C.swap.set = C.set := by
  unfold set; exact union_comm _ _

end YChain

/-- The mirror (Y2) ending. -/
def Y2End.swap {M : Molecule V D} {C : YChain M} (E : Y2End C) : Y2End C.swap where
  x := E.y
  y := E.x
  hx := E.hy
  hy := E.hx
  hxo := by rw [C.swap_set]; exact E.hyo
  hyo := by rw [C.swap_set]; exact E.hxo
  far := E.far.symm
  deg_a := E.deg_b
  deg_b := E.deg_a

end WaveTurbulence.MoleProp4
