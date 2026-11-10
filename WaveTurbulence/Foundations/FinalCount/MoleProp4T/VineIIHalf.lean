/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.VineIITemplate
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.ChainResidual
import Mathlib.Tactic

/-! # A (Y) sequence ending in (Y1) case 1 is a half-closed vine (II)

DH23 L1959: "cannot be (Y1) case 1 because then `𝕄` would be formed from vine (II) by removing the two joints of a
vine (II) and adding one new bond between the two atoms connected to one of the joints". With B2's template (F72,
`m ≥ 1` rungs, so the length-one chain is the `m = 1` vine): a connected molecule whose complete (Y) sequence ends in
(Y1) case 1 is, as an undirected multigraph, the half-closure of `expand .II [n]`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **`𝕄` is formed from vine (II)** by removing its two joints and adding one bond between the two atoms joined to
one joint (DH23 L1838; B2 template, F72): its undirected bond multiset is that of the half-closure of `expand .II [k]`
for some `k`. -/
def IsVineIIHalfClosure (M : Molecule V D) : Prop :=
  ∃ k : ℕ, ∃ f : V → ℕ, Set.InjOn f M.atoms ∧ M.atoms.image f = range (4 + 2 * k) \ {0, 1} ∧
    (M.groupBonds M.atoms).map (Sym2.map f) = halfClosureIIBonds k

omit [DecidableEq D] in
/-- The bond multiset counts bonds. -/
theorem count_groupBonds_atoms (M : Molecule V D) (p q : V) :
    (M.groupBonds M.atoms).count s(p, q) = M.bondsBetween p q := by
  classical
  unfold Molecule.groupBonds Molecule.bondsBetween Molecule.bonds
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, Molecule.InGroup, M.atom_mem, and_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

namespace YChain
variable {M : Molecule V D} (C : YChain M) (h6 : M.deg (C.a C.n) + M.deg (C.b C.n) = 6)
include h6

omit [DecidableEq D] in
/-- In a (Y1) case 1 chain, every bond of `a i` goes to `nbA i`. -/
theorem mate_mem_nbA_c1 {i : ℕ} (hi : i ≤ C.n) {z : D} (hz : M.atom z = C.a i) : M.atom (M.mate z) ∈ C.nbA i := by
  classical
  rcases Nat.lt_or_ge i C.n with hlt | hge
  · exact C.mate_mem_nbA_of_lt hlt hz
  · have : i = C.n := le_antisymm hi hge
    subst this
    by_contra hno
    have ha := C.card_away_last_a
    have hb := C.card_away_last_b
    have h0 : ((M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n).card = 0 := by omega
    have hzm : z ∈ (M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hz⟩, hno⟩
    rw [card_eq_zero] at h0; rw [h0] at hzm; simp at hzm

omit [DecidableEq D] in
theorem mate_mem_nbB_c1 {i : ℕ} (hi : i ≤ C.n) {z : D} (hz : M.atom z = C.b i) : M.atom (M.mate z) ∈ C.nbB i := by
  have h6' : M.deg (C.swap.a C.swap.n) + M.deg (C.swap.b C.swap.n) = 6 := by
    change M.deg (C.b C.n) + M.deg (C.a C.n) = 6; omega
  exact C.swap.mate_mem_nbA_c1 h6' hi hz

end YChain


namespace YChain
variable {M : Molecule V D} (C : YChain M)

/-- The chain's bond multiset pieces. -/
def tripleE : Sym2 V := s(C.a 0, C.b 0)
def rungE (i : ℕ) : Sym2 V := s(C.a (i + 1), C.b (i + 1))
def railAE (i : ℕ) : Sym2 V := s(C.a i, C.a (i + 1))
def railBE (i : ℕ) : Sym2 V := s(C.b i, C.b (i + 1))

/-- The chain's bonds, as a finset of unordered pairs. -/
def bondSet : Finset (Sym2 V) :=
  insert C.tripleE ((range C.n).image C.rungE ∪ (range C.n).image C.railAE ∪ (range C.n).image C.railBE)

omit [DecidableEq D] in
theorem triple_notMem : C.tripleE ∉ (range C.n).image C.rungE ∪ (range C.n).image C.railAE ∪
    (range C.n).image C.railBE := by
  simp only [mem_union, mem_image, mem_range, not_or, not_exists, not_and]
  refine ⟨⟨fun i hi h => ?_, fun i hi h => ?_⟩, fun i hi h => ?_⟩ <;>
    simp only [rungE, railAE, railBE, tripleE] at h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := C.inj_a _ (by omega) _ (by omega) h1; omega
  · exact C.ne_ab _ (by omega) _ (by omega) h1
  · exact C.ne_ab _ (by omega) _ (by omega) h2
  · exact C.ne_ab _ (by omega) _ (by omega) h1
  · exact C.ne_ab _ (by omega) _ (by omega) h1.symm
  · exact C.ne_ab _ (by omega) _ (by omega) h2.symm

omit [DecidableEq D] in
theorem disj_rung_railA : Disjoint ((range C.n).image C.rungE) ((range C.n).image C.railAE) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨i, hi, rfl⟩ := mem_image.mp he
  obtain ⟨j, hj, h⟩ := mem_image.mp he'
  rw [mem_range] at hi hj
  simp only [rungE, railAE] at h
  rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact C.ne_ab (j + 1) (by omega) (i + 1) (by omega) h2
  · exact C.ne_ab j (by omega) (i + 1) (by omega) h1

omit [DecidableEq D] in
theorem disj_rungA_railB : Disjoint ((range C.n).image C.rungE ∪ (range C.n).image C.railAE)
    ((range C.n).image C.railBE) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨j, hj, h⟩ := mem_image.mp he'
  rw [mem_range] at hj
  rcases mem_union.mp he with he | he
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp he
    rw [mem_range] at hi
    simp only [rungE, railBE] at h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact C.ne_ab _ (by omega) _ (by omega) h1.symm
    · exact C.ne_ab _ (by omega) _ (by omega) h2.symm
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp he
    rw [mem_range] at hi
    simp only [railAE, railBE] at h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact C.ne_ab _ (by omega) _ (by omega) h1.symm
    · exact C.ne_ab _ (by omega) _ (by omega) h1.symm

omit [DecidableEq D] in
theorem rungE_injOn : Set.InjOn C.rungE (range C.n) := by
  intro i hi j hj h
  rw [coe_range, Set.mem_Iio] at hi hj
  simp only [rungE] at h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · have := C.inj_a _ (by omega) _ (by omega) h1; omega
  · exact absurd h1 (C.ne_ab _ (by omega) _ (by omega))

omit [DecidableEq D] in
theorem railAE_injOn : Set.InjOn C.railAE (range C.n) := by
  intro i hi j hj h
  rw [coe_range, Set.mem_Iio] at hi hj
  simp only [railAE] at h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact C.inj_a _ (by omega) _ (by omega) h1
  · have := C.inj_a _ (by omega) _ (by omega) h1
    have := C.inj_a _ (by omega) _ (by omega) h2
    omega

omit [DecidableEq D] in
theorem railBE_injOn : Set.InjOn C.railBE (range C.n) := by
  intro i hi j hj h
  rw [coe_range, Set.mem_Iio] at hi hj
  simp only [railBE] at h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact C.inj_b _ (by omega) _ (by omega) h1
  · have := C.inj_b _ (by omega) _ (by omega) h1
    have := C.inj_b _ (by omega) _ (by omega) h2
    omega

omit [DecidableEq D] in
/-- **Every bond of a (Y1) case 1 chain covering `𝕄` is a chain bond.** -/
theorem toFinset_sub_bondSet (h6 : M.deg (C.a C.n) + M.deg (C.b C.n) = 6) (hcover : C.set = M.atoms) :
    (M.groupBonds M.atoms).toFinset ⊆ C.bondSet := by
  intro e he
  rw [Multiset.mem_toFinset] at he
  unfold Molecule.groupBonds at he
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp he
  have hx : M.atom x ∈ C.set := hcover ▸ M.atom_mem x
  have hends : M.ends x = s(M.atom x, M.atom (M.mate x)) := rfl
  unfold bondSet
  rw [mem_insert, mem_union, mem_union, mem_image, mem_image, mem_image, hends]
  obtain ⟨i, hi, hxi | hxi⟩ := C.mem_set.mp hx
  · have hn := C.mate_mem_nbA_c1 h6 hi hxi
    rw [Y2End.mem_nbA_iff] at hn
    rcases hn with hq | ⟨h0, hq⟩ | ⟨h0, hq⟩ <;> rw [hxi, hq]
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · left; rfl
      · right; left; left
        exact ⟨i - 1, mem_range.mpr (by omega), by simp only [rungE, Nat.sub_add_cancel hpos]⟩
    · right; left; right
      exact ⟨i - 1, mem_range.mpr (by omega), by simp only [railAE, Nat.sub_add_cancel h0]; exact Sym2.eq_swap⟩
    · right; left; right; exact ⟨i, mem_range.mpr h0, rfl⟩
  · have hn := C.mate_mem_nbB_c1 h6 hi hxi
    rw [Y2End.mem_nbB_iff] at hn
    rcases hn with hq | ⟨h0, hq⟩ | ⟨h0, hq⟩ <;> rw [hxi, hq]
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · left; exact Sym2.eq_swap
      · right; left; left
        exact ⟨i - 1, mem_range.mpr (by omega), by simp only [rungE, Nat.sub_add_cancel hpos]; exact Sym2.eq_swap⟩
    · right; right
      exact ⟨i - 1, mem_range.mpr (by omega), by simp only [railBE, Nat.sub_add_cancel h0]; exact Sym2.eq_swap⟩
    · right; right; exact ⟨i, mem_range.mpr h0, rfl⟩

omit [DecidableEq D] in
/-- **The bond multiset of a (Y1) case 1 chain covering `𝕄`.** -/
theorem groupBonds_eq (h6 : M.deg (C.a C.n) + M.deg (C.b C.n) = 6) (hcover : C.set = M.atoms) :
    M.groupBonds M.atoms = 3 • {C.tripleE} +
      ∑ i ∈ range C.n, (2 • {C.rungE i} + {C.railAE i} + {C.railBE i}) := by
  classical
  set G := M.groupBonds M.atoms
  have hG : G = ∑ e ∈ C.bondSet, G.count e • {e} := by
    conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq G]
    exact sum_subset (C.toFinset_sub_bondSet h6 hcover) fun e _ he => by
      rw [Multiset.count_eq_zero.mpr (fun h => he (Multiset.mem_toFinset.mpr h)), zero_nsmul]
  rw [hG]
  unfold bondSet
  rw [sum_insert C.triple_notMem, sum_union C.disj_rungA_railB, sum_union C.disj_rung_railA,
    sum_image C.rungE_injOn, sum_image C.railAE_injOn, sum_image C.railBE_injOn]
  have ht : G.count C.tripleE = 3 := by
    simp only [G, tripleE, count_groupBonds_atoms]; exact C.triple
  have hr : ∀ i ∈ range C.n, G.count (C.rungE i) = 2 := fun i hi => by
    simp only [G, rungE, count_groupBonds_atoms]; exact C.rung (i + 1) (by omega) (by simpa using hi)
  have ha : ∀ i ∈ range C.n, G.count (C.railAE i) = 1 := fun i hi => by
    simp only [G, railAE, count_groupBonds_atoms]; exact (C.rail i (by simpa using hi)).1
  have hb : ∀ i ∈ range C.n, G.count (C.railBE i) = 1 := fun i hi => by
    simp only [G, railBE, count_groupBonds_atoms]; exact (C.rail i (by simpa using hi)).2
  have s1 : ∑ i ∈ range C.n, G.count (C.rungE i) • {C.rungE i} = ∑ i ∈ range C.n, 2 • ({C.rungE i} : Multiset (Sym2 V)) :=
    sum_congr rfl fun i hi => by rw [hr i hi]
  have s2 : ∑ i ∈ range C.n, G.count (C.railAE i) • {C.railAE i} = ∑ i ∈ range C.n, 1 • ({C.railAE i} : Multiset (Sym2 V)) :=
    sum_congr rfl fun i hi => by rw [ha i hi]
  have s3 : ∑ i ∈ range C.n, G.count (C.railBE i) • {C.railBE i} = ∑ i ∈ range C.n, 1 • ({C.railBE i} : Multiset (Sym2 V)) :=
    sum_congr rfl fun i hi => by rw [hb i hi]
  rw [ht, s1, s2, s3, sum_add_distrib, sum_add_distrib]
  simp only [one_nsmul]

/-- The labelling of the chain atoms by the template's atoms. -/
noncomputable def label (v : V) : ℕ :=
  if h : ∃ i, i ≤ C.n ∧ C.a i = v then labA C.n (Nat.find h)
  else if h' : ∃ i, i ≤ C.n ∧ C.b i = v then labB C.n (Nat.find h') else 0

omit [DecidableEq D] in
theorem label_a {i : ℕ} (hi : i ≤ C.n) : C.label (C.a i) = labA C.n i := by
  have h : ∃ j, j ≤ C.n ∧ C.a j = C.a i := ⟨i, hi, rfl⟩
  unfold label
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  have hs := Nat.find_spec h
  exact C.inj_a _ hs.1 i hi hs.2

omit [DecidableEq D] in
theorem label_b {i : ℕ} (hi : i ≤ C.n) : C.label (C.b i) = labB C.n i := by
  have hna : ¬ ∃ j, j ≤ C.n ∧ C.a j = C.b i := fun ⟨j, hj, h⟩ => C.ne_ab j hj i hi h
  have h : ∃ j, j ≤ C.n ∧ C.b j = C.b i := ⟨i, hi, rfl⟩
  unfold label
  rw [dite_eq_right_of_eq_false (eq_false hna), dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  have hs := Nat.find_spec h
  exact C.inj_b _ hs.1 i hi hs.2

omit [DecidableEq D] in
theorem label_range {v : V} (hv : v ∈ C.set) : 2 ≤ C.label v ∧ C.label v < 4 + 2 * C.n := by
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hv
  · rw [C.label_a hi]; unfold labA; split_ifs <;> omega
  · rw [C.label_b hi]; unfold labB; split_ifs <;> omega

omit [DecidableEq D] in
theorem label_injOn : Set.InjOn C.label C.set := by
  intro u hu v hv h
  obtain ⟨i, hi, rfl | rfl⟩ := C.mem_set.mp hu <;> obtain ⟨j, hj, rfl | rfl⟩ := C.mem_set.mp hv
  · rw [C.label_a hi, C.label_a hj] at h; unfold labA at h
    rw [show i = j by split_ifs at h <;> omega]
  · rw [C.label_a hi, C.label_b hj] at h; unfold labA labB at h; exfalso; split_ifs at h <;> omega
  · rw [C.label_b hi, C.label_a hj] at h; unfold labA labB at h; exfalso; split_ifs at h <;> omega
  · rw [C.label_b hi, C.label_b hj] at h; unfold labB at h
    rw [show i = j by split_ifs at h <;> omega]

omit [DecidableEq D] in
theorem label_image : C.set.image C.label = range (4 + 2 * C.n) \ {0, 1} := by
  ext x
  simp only [mem_image, mem_sdiff, mem_range, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := C.label_range hv
    omega
  · rintro ⟨hx, h0, h1⟩
    by_cases h2 : x = 2
    · exact ⟨C.a 0, C.a_mem (Nat.zero_le _), by rw [C.label_a (Nat.zero_le _), h2]; rfl⟩
    by_cases h3 : x = 3
    · exact ⟨C.b 0, C.b_mem (Nat.zero_le _), by rw [C.label_b (Nat.zero_le _), h3]; rfl⟩
    by_cases h4 : x ≤ 3 + C.n
    · refine ⟨C.a (x - 3), C.a_mem (by omega), ?_⟩
      rw [C.label_a (by omega)]; unfold labA; split_ifs <;> omega
    · refine ⟨C.b (x - 3 - C.n), C.b_mem (by omega), ?_⟩
      rw [C.label_b (by omega)]; unfold labB; split_ifs <;> omega

omit [DecidableEq D] in
/-- **A (Y1) case 1 chain covering `𝕄` makes `𝕄` a half-closed vine (II)** (with `m = n + 1` rungs). -/
theorem isVineIIHalfClosure (h6 : M.deg (C.a C.n) + M.deg (C.b C.n) = 6) (hcover : C.set = M.atoms) :
    IsVineIIHalfClosure M := by
  refine ⟨C.n, C.label, hcover ▸ C.label_injOn, hcover ▸ C.label_image, ?_⟩
  rw [halfClosureIIBonds_eq, C.groupBonds_eq h6 hcover, ladderBonds]
  simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
  have hmap : ∀ s : Multiset (Sym2 V), Multiset.map (Sym2.map C.label) s =
      Multiset.mapAddMonoidHom (Sym2.map C.label) s := fun _ => rfl
  rw [hmap (∑ i ∈ range C.n, _), map_sum]
  simp only [Multiset.mapAddMonoidHom_apply, Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
    tripleE, rungE, railAE, railBE, Sym2.map_mk]
  rw [C.label_a (Nat.zero_le _), C.label_b (Nat.zero_le _)]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < C.n := mem_range.mp hi
  rw [C.label_a (by omega), C.label_b (by omega), C.label_a (by omega), C.label_b (by omega)]

end YChain

end WaveTurbulence.MoleProp4
