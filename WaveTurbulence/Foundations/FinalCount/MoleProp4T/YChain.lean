/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExit
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExit
import Mathlib.Tactic

/-! # (Y) sequences as chains (DH23 L1929, Figure YOper)

A (Y) sequence starts at a triple bond `(v₁, v₂)` and, while each (Y2) creates a new triple bond, continues at it. The
atoms it removes form a chain: pairs `(a i, b i)`, `i ≤ n`, with `a 0 ≡ b 0` a triple bond, `a i = b i` double bonds for
`i ≥ 1` (they become triple when the previous pair is removed and the new bond added), single rails `a i – a (i+1)`,
`b i – b (i+1)`, and every pair before the last saturated (degree four). The last pair carries the ending: (Y2) (two
extra single bonds to distinct atoms), or (Y1) case 1 (no extra bond), case 2 (one extra bond), case 3 (two extra
bonds to one atom). The post molecule `𝕄′` of DH23 is the chain removed and, for (Y2), one bond added between the
two far ends matching the removed directions.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **A (Y) chain** of `n + 1` pairs (DH23 L1929). -/
structure YChain (M : Molecule V D) where
  n : ℕ
  a : ℕ → V
  b : ℕ → V
  inj_a : ∀ i ≤ n, ∀ j ≤ n, a i = a j → i = j
  inj_b : ∀ i ≤ n, ∀ j ≤ n, b i = b j → i = j
  ne_ab : ∀ i ≤ n, ∀ j ≤ n, a i ≠ b j
  mem : ∀ i ≤ n, a i ∈ M.atoms ∧ b i ∈ M.atoms
  triple : M.bondsBetween (a 0) (b 0) = 3
  rung : ∀ i, 0 < i → i ≤ n → M.bondsBetween (a i) (b i) = 2
  rail : ∀ i < n, M.bondsBetween (a i) (a (i + 1)) = 1 ∧ M.bondsBetween (b i) (b (i + 1)) = 1
  sat : ∀ i < n, M.deg (a i) = 4 ∧ M.deg (b i) = 4

namespace YChain
variable {M : Molecule V D} (C : YChain M)

/-- The removed atoms. -/
def set : Finset V := (range (C.n + 1)).image C.a ∪ (range (C.n + 1)).image C.b

omit [DecidableEq D] in
theorem mem_set {v : V} : v ∈ C.set ↔ ∃ i ≤ C.n, v = C.a i ∨ v = C.b i := by
  unfold set
  simp only [mem_union, mem_image, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

omit [DecidableEq D] in
theorem a_mem {i : ℕ} (hi : i ≤ C.n) : C.a i ∈ C.set := C.mem_set.mpr ⟨i, hi, Or.inl rfl⟩
omit [DecidableEq D] in
theorem b_mem {i : ℕ} (hi : i ≤ C.n) : C.b i ∈ C.set := C.mem_set.mpr ⟨i, hi, Or.inr rfl⟩

omit [DecidableEq D] in
theorem set_sub : C.set ⊆ M.atoms := by
  intro v hv
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
  exacts [(C.mem i hi).1, (C.mem i hi).2]

omit [DecidableEq D] in
/-- A bond count `≥ 1` gives an adjacency inside any set containing both ends. -/
theorem piece_adj {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v)
    (h : 1 ≤ M.bondsBetween u v) : (piece M S).Adj u v := by
  rw [← Degen.card_neighborDarts M hne] at h
  obtain ⟨z, hz⟩ := card_pos.mp h
  obtain ⟨hza, hzm⟩ := (Degen.mem_neighborDarts M u v z).mp hz
  exact ⟨pieceDart M S z ⟨hza ▸ hu, hzm ▸ hv⟩, hza, hzm⟩

omit [DecidableEq D] in
/-- **The chain piece is connected.** -/
theorem piece_connected : ∀ u ∈ C.set, ∀ v ∈ C.set, (piece M C.set).SameComponent u v := by
  have hab : ∀ i ≤ C.n, (piece M C.set).SameComponent (C.a i) (C.b i) := by
    intro i hi
    refine Relation.EqvGen.rel _ _ (piece_adj (C.a_mem hi) (C.b_mem hi) (C.ne_ab i hi i hi) ?_)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [C.triple]; norm_num
    · rw [C.rung i hpos hi]; norm_num
  have ha : ∀ i ≤ C.n, (piece M C.set).SameComponent (C.a 0) (C.a i) := by
    intro i hi
    induction i with
    | zero => exact Relation.EqvGen.refl _
    | succ k ih =>
      have hk : k ≤ C.n := by omega
      have hne : C.a k ≠ C.a (k + 1) := fun h => by have := C.inj_a k hk (k + 1) hi h; omega
      exact Relation.EqvGen.trans _ _ _ (ih hk) (Relation.EqvGen.rel _ _
        (piece_adj (C.a_mem hk) (C.a_mem hi) hne (by rw [(C.rail k (by omega)).1])))
  have hall : ∀ v ∈ C.set, (piece M C.set).SameComponent (C.a 0) v := by
    intro v hv
    obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
    · exact ha i hi
    · exact Relation.EqvGen.trans _ _ _ (ha i hi) (hab i hi)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall u hu)) (hall v hv)

/-- The chain neighbours of `a i`. -/
def nbA (i : ℕ) : Finset V :=
  insert (C.b i) ((if 0 < i then {C.a (i - 1)} else ∅) ∪ (if i < C.n then {C.a (i + 1)} else ∅))

/-- The chain neighbours of `b i`. -/
def nbB (i : ℕ) : Finset V :=
  insert (C.a i) ((if 0 < i then {C.b (i - 1)} else ∅) ∪ (if i < C.n then {C.b (i + 1)} else ∅))

omit [DecidableEq D] in
theorem nbA_sub {i : ℕ} (hi : i ≤ C.n) : C.nbA i ⊆ C.set := by
  intro v hv
  simp only [nbA, mem_insert, mem_union] at hv
  rcases hv with rfl | hv | hv
  · exact C.b_mem hi
  · split_ifs at hv with h
    · rw [mem_singleton.mp hv]; exact C.a_mem (by omega)
    · simp at hv
  · split_ifs at hv with h
    · rw [mem_singleton.mp hv]; exact C.a_mem (by omega)
    · simp at hv

omit [DecidableEq D] in
theorem nbB_sub {i : ℕ} (hi : i ≤ C.n) : C.nbB i ⊆ C.set := by
  intro v hv
  simp only [nbB, mem_insert, mem_union] at hv
  rcases hv with rfl | hv | hv
  · exact C.a_mem hi
  · split_ifs at hv with h
    · rw [mem_singleton.mp hv]; exact C.b_mem (by omega)
    · simp at hv
  · split_ifs at hv with h
    · rw [mem_singleton.mp hv]; exact C.b_mem (by omega)
    · simp at hv

omit [DecidableEq D] in
theorem nbA_notMem {i : ℕ} (hi : i ≤ C.n) : C.a i ∉ C.nbA i := by
  simp only [nbA, mem_insert, mem_union, not_or]
  refine ⟨C.ne_ab i hi i hi, ?_, ?_⟩
  · split_ifs with h
    · simp only [mem_singleton]; intro e; have := C.inj_a i hi (i - 1) (by omega) e; omega
    · simp
  · split_ifs with h
    · simp only [mem_singleton]; intro e; have := C.inj_a i hi (i + 1) (by omega) e; omega
    · simp

omit [DecidableEq D] in
theorem nbB_notMem {i : ℕ} (hi : i ≤ C.n) : C.b i ∉ C.nbB i := by
  simp only [nbB, mem_insert, mem_union, not_or]
  refine ⟨fun e => C.ne_ab i hi i hi e.symm, ?_, ?_⟩
  · split_ifs with h
    · simp only [mem_singleton]; intro e; have := C.inj_b i hi (i - 1) (by omega) e; omega
    · simp
  · split_ifs with h
    · simp only [mem_singleton]; intro e; have := C.inj_b i hi (i + 1) (by omega) e; omega
    · simp

omit [DecidableEq D] in
/-- The bonds of `a i` to its chain neighbours. -/
theorem sum_nbA {i : ℕ} (hi : i ≤ C.n) :
    ∑ w ∈ C.nbA i, M.bondsBetween (C.a i) w =
      (if i = 0 then 3 else 2) + (if 0 < i then 1 else 0) + (if i < C.n then 1 else 0) := by
  have bc := fun u v => Degen.bondsBetween_comm M u v
  have hb : C.b i ∉ (if 0 < i then {C.a (i - 1)} else ∅) ∪ (if i < C.n then ({C.a (i + 1)} : Finset V) else ∅) := by
    simp only [mem_union, not_or]
    constructor
    · split_ifs with h
      · simp only [mem_singleton]; exact fun e => C.ne_ab (i - 1) (by omega) i hi e.symm
      · simp
    · split_ifs with h
      · simp only [mem_singleton]; exact fun e => C.ne_ab (i + 1) (by omega) i hi e.symm
      · simp
  have hd : Disjoint (if 0 < i then {C.a (i - 1)} else ∅) (if i < C.n then ({C.a (i + 1)} : Finset V) else ∅) := by
    split_ifs with h1 h2 <;> simp only [disjoint_singleton, disjoint_empty_left, disjoint_empty_right]
    intro e; have := C.inj_a _ (by omega) _ (by omega) e; omega
  unfold nbA
  rw [sum_insert hb, sum_union hd]
  have h0 : M.bondsBetween (C.a i) (C.b i) = if i = 0 then 3 else 2 := by
    split_ifs with h
    · subst h; exact C.triple
    · exact C.rung i (by omega) hi
  rw [h0, add_assoc]
  congr 1
  congr 1
  · split_ifs with h
    · rw [sum_singleton, bc]; exact (C.rail (i - 1) (by omega)).1 |> fun r => by
        rwa [show i - 1 + 1 = i by omega] at r
    · simp
  · split_ifs with h
    · rw [sum_singleton]; exact (C.rail i h).1
    · simp

omit [DecidableEq D] in
theorem sum_nbB {i : ℕ} (hi : i ≤ C.n) :
    ∑ w ∈ C.nbB i, M.bondsBetween (C.b i) w =
      (if i = 0 then 3 else 2) + (if 0 < i then 1 else 0) + (if i < C.n then 1 else 0) := by
  have bc := fun u v => Degen.bondsBetween_comm M u v
  have hb : C.a i ∉ (if 0 < i then {C.b (i - 1)} else ∅) ∪ (if i < C.n then ({C.b (i + 1)} : Finset V) else ∅) := by
    simp only [mem_union, not_or]
    constructor
    · split_ifs with h
      · simp only [mem_singleton]; exact fun e => C.ne_ab i hi (i - 1) (by omega) e
      · simp
    · split_ifs with h
      · simp only [mem_singleton]; exact fun e => C.ne_ab i hi (i + 1) (by omega) e
      · simp
  have hd : Disjoint (if 0 < i then {C.b (i - 1)} else ∅) (if i < C.n then ({C.b (i + 1)} : Finset V) else ∅) := by
    split_ifs with h1 h2 <;> simp only [disjoint_singleton, disjoint_empty_left, disjoint_empty_right]
    intro e; have := C.inj_b _ (by omega) _ (by omega) e; omega
  unfold nbB
  rw [sum_insert hb, sum_union hd]
  have h0 : M.bondsBetween (C.b i) (C.a i) = if i = 0 then 3 else 2 := by
    rw [bc]
    split_ifs with h
    · subst h; exact C.triple
    · exact C.rung i (by omega) hi
  rw [h0, add_assoc]
  congr 1
  congr 1
  · split_ifs with h
    · rw [sum_singleton, bc]; exact (C.rail (i - 1) (by omega)).2 |> fun r => by
        rwa [show i - 1 + 1 = i by omega] at r
    · simp
  · split_ifs with h
    · rw [sum_singleton]; exact (C.rail i h).2
    · simp

omit [DecidableEq D] in
/-- Darts of `v` towards `S` number `∑_{w ∈ S} bonds(v, w)`. -/
theorem card_darts_toward (v : V) (S : Finset V) (hvS : v ∉ S) :
    ((M.dartsAt v).filter fun z => M.atom (M.mate z) ∈ S).card = ∑ w ∈ S, M.bondsBetween v w := by
  classical
  rw [card_eq_sum_card_fiberwise (s := (M.dartsAt v).filter fun z => M.atom (M.mate z) ∈ S) (t := S)
    (f := fun z => M.atom (M.mate z)) (fun z hz => (mem_filter.mp hz).2)]
  refine sum_congr rfl fun w hw => ?_
  have hvw : v ≠ w := fun h => hvS (h ▸ hw)
  rw [← Degen.card_neighborDarts M hvw]
  congr 1
  ext z
  simp only [mem_filter, Degen.mem_neighborDarts, Molecule.dartsAt, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hw⟩, h2⟩

omit [DecidableEq D] in
theorem card_darts_away (v : V) (S : Finset V) (hvS : v ∉ S) :
    ((M.dartsAt v).filter fun z => M.atom (M.mate z) ∉ S).card + ∑ w ∈ S, M.bondsBetween v w = M.deg v := by
  rw [← card_darts_toward v S hvS, add_comm]
  exact card_filter_add_card_filter_not _

omit [DecidableEq D] in
/-- No dart leaves the chain at a saturated pair. -/
theorem not_cross_of_lt {z : D} {i : ℕ} (hi : i < C.n) (hz : M.atom z = C.a i ∨ M.atom z = C.b i) :
    M.atom (M.mate z) ∈ C.set := by
  rcases hz with hz | hz
  · have h := card_darts_away (M := M) (C.a i) (C.nbA i) (C.nbA_notMem hi.le)
    rw [C.sum_nbA hi.le, (C.sat i hi).1] at h
    have h0 : ((M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i).card = 0 := by
      split_ifs at h <;> omega
    by_contra hout
    have hzm : z ∈ (M.dartsAt (C.a i)).filter fun z => M.atom (M.mate z) ∉ C.nbA i :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, fun h' => hout (C.nbA_sub hi.le h')⟩
    rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm
  · have h := card_darts_away (M := M) (C.b i) (C.nbB i) (C.nbB_notMem hi.le)
    rw [C.sum_nbB hi.le, (C.sat i hi).2] at h
    have h0 : ((M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i).card = 0 := by
      split_ifs at h <;> omega
    by_contra hout
    have hzm : z ∈ (M.dartsAt (C.b i)).filter fun z => M.atom (M.mate z) ∉ C.nbB i :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, fun h' => hout (C.nbB_sub hi.le h')⟩
    rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm

omit [DecidableEq D] in
/-- At the last pair, the darts leaving the chain number `deg − 3`. -/
theorem card_away_last_a :
    ((M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n).card + 3 = M.deg (C.a C.n) := by
  have h := card_darts_away (M := M) (C.a C.n) (C.nbA C.n) (C.nbA_notMem le_rfl)
  rw [C.sum_nbA le_rfl] at h
  split_ifs at h <;> omega

omit [DecidableEq D] in
theorem card_away_last_b :
    ((M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n).card + 3 = M.deg (C.b C.n) := by
  have h := card_darts_away (M := M) (C.b C.n) (C.nbB C.n) (C.nbB_notMem le_rfl)
  rw [C.sum_nbB le_rfl] at h
  split_ifs at h <;> omega

end YChain
end WaveTurbulence.MoleProp4
