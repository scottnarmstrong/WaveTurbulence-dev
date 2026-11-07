/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Common
import Mathlib.Tactic

/-! # The upper part of a (Y2) chain as a ladder of double bonds

From pair `j` on, a (Y2)-ended chain is a `Ladder3` in any molecule `N'` that has the chain's bonds and degrees there,
except that pair `j` is a double bond of two degree-three atoms. This is the situation after the bond `ℓ` (or the
part of the chain below it) has been removed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace YChain
variable {M : Molecule V D} (C : YChain M)

/-- The pairs from `j` on. -/
def upper (j : ℕ) : Finset V := ((Icc j C.n).image C.a) ∪ ((Icc j C.n).image C.b)

omit [DecidableEq D] in
theorem mem_upper {j : ℕ} {v : V} : v ∈ C.upper j ↔ ∃ i, j ≤ i ∧ i ≤ C.n ∧ (v = C.a i ∨ v = C.b i) := by
  unfold upper
  simp only [mem_union, mem_image, mem_Icc]
  constructor
  · rintro (⟨i, ⟨h1, h2⟩, rfl⟩ | ⟨i, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨i, h1, h2, Or.inl rfl⟩
    · exact ⟨i, h1, h2, Or.inr rfl⟩
  · rintro ⟨i, h1, h2, rfl | rfl⟩
    · exact Or.inl ⟨i, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨i, ⟨h1, h2⟩, rfl⟩

omit [DecidableEq D] in
theorem upper_zero : C.upper 0 = C.set := by
  ext v; rw [C.mem_upper, C.mem_set]
  constructor
  · rintro ⟨i, _, h2, h⟩; exact ⟨i, h2, h⟩
  · rintro ⟨i, h2, h⟩; exact ⟨i, Nat.zero_le _, h2, h⟩

omit [DecidableEq D] in
theorem low_union_upper {k : ℕ} (hk : k < C.n) : (C.low k hk.le).set ∪ C.upper (k + 1) = C.set := by
  ext v
  rw [mem_union, (C.low k hk.le).mem_set, C.mem_upper, C.mem_set]
  change (∃ i ≤ k, v = C.a i ∨ v = C.b i) ∨ _ ↔ _
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, _, h2, h⟩)
    · exact ⟨i, by omega, h⟩
    · exact ⟨i, h2, h⟩
  · rintro ⟨i, hi, h⟩
    rcases Nat.lt_or_ge k i with h' | h'
    · exact Or.inr ⟨i, h', hi, h⟩
    · exact Or.inl ⟨i, h', h⟩

end YChain

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

/-- **The chain from pair `j` on as a `Ladder3` of a molecule with the same bonds there.** -/
def ladderFrom {W : Type*} [Fintype W] [DecidableEq W] (N' : Molecule V W) (j : ℕ) (hj : j ≤ C.n)
    (hmem : ∀ i, j ≤ i → i ≤ C.n → C.a i ∈ N'.atoms ∧ C.b i ∈ N'.atoms)
    (hrung : N'.bondsBetween (C.a j) (C.b j) = 2)
    (hbb : ∀ p q : V, p ∈ C.upper j → q ∈ C.upper j → s(p, q) ≠ s(C.a j, C.b j) →
      N'.bondsBetween p q = M.bondsBetween p q)
    (hdeg0 : N'.deg (C.a j) = 3 ∧ N'.deg (C.b j) = 3)
    (hdeg : ∀ i, j < i → i ≤ C.n → N'.deg (C.a i) = M.deg (C.a i) ∧ N'.deg (C.b i) = M.deg (C.b i)) :
    Ladder3 N' where
  m := C.n - j
  a i := C.a (j + i)
  b i := C.b (j + i)
  inj_a i hi k hk h := by have := C.inj_a (j + i) (by omega) (j + k) (by omega) h; omega
  inj_b i hi k hk h := by have := C.inj_b (j + i) (by omega) (j + k) (by omega) h; omega
  ne_ab i hi k hk := C.ne_ab (j + i) (by omega) (j + k) (by omega)
  mem i hi := hmem (j + i) (by omega) (by omega)
  rung i hi := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using hrung
    · have ha : C.a (j + i) ∈ C.upper j := C.mem_upper.mpr ⟨j + i, by omega, by omega, Or.inl rfl⟩
      have hb : C.b (j + i) ∈ C.upper j := C.mem_upper.mpr ⟨j + i, by omega, by omega, Or.inr rfl⟩
      rw [hbb _ _ ha hb (sym2_ne_of_left (fun h => by have := C.inj_a _ (by omega) j hj h; omega)
        (C.ne_ab _ (by omega) j hj))]
      exact C.rung (j + i) (by omega) (by omega)
  rail i hi := by
    have hmem' : ∀ t, j ≤ t → t ≤ C.n → C.a t ∈ C.upper j ∧ C.b t ∈ C.upper j := fun t h1 h2 =>
      ⟨C.mem_upper.mpr ⟨t, h1, h2, Or.inl rfl⟩, C.mem_upper.mpr ⟨t, h1, h2, Or.inr rfl⟩⟩
    have e1 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).1 (hmem' (j + (i + 1)) (by omega) (by omega)).1
      (sym2_ne_of_right (fun h => by have := C.inj_a _ (by omega) j hj h; omega) (C.ne_ab _ (by omega) j hj))
    have e2 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).2 (hmem' (j + (i + 1)) (by omega) (by omega)).2
      (sym2_ne_of_right (fun h => C.ne_ab j hj _ (by omega) h.symm)
        (fun h => by have := C.inj_b _ (by omega) j hj h; omega))
    rw [e1, e2]
    exact C.rail (j + i) (by omega)
  deg0 := by simpa using hdeg0
  deg4 i h1 h2 := by
    rw [(hdeg (j + i) (by omega) (by omega)).1, (hdeg (j + i) (by omega) (by omega)).2]
    exact ⟨E.deg_four _ (C.a_mem (by omega)), E.deg_four _ (C.b_mem (by omega))⟩
  cross i hi k hk := by
    have hmem' : ∀ t, j ≤ t → t ≤ C.n → C.a t ∈ C.upper j ∧ C.b t ∈ C.upper j := fun t h1 h2 =>
      ⟨C.mem_upper.mpr ⟨t, h1, h2, Or.inl rfl⟩, C.mem_upper.mpr ⟨t, h1, h2, Or.inr rfl⟩⟩
    have e1 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).1 (hmem' (j + k) (by omega) (by omega)).2
      (sym2_ne_of_left (fun h => by have := C.inj_a _ (by omega) j hj h; omega) (C.ne_ab _ (by omega) j hj))
    have e2 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).2 (hmem' (j + k) (by omega) (by omega)).1
      (sym2_ne_of_left (fun h => C.ne_ab j hj _ (by omega) h.symm)
        (fun h => by have := C.inj_b _ (by omega) j hj h; omega))
    rw [e1, e2, Degen.bondsBetween_comm M (C.b _)]
    exact ⟨E.bonds_a_b (by omega) (by omega) (by omega), E.bonds_a_b (by omega) (by omega) (by omega)⟩
  long i hi k hk := by
    have hmem' : ∀ t, j ≤ t → t ≤ C.n → C.a t ∈ C.upper j ∧ C.b t ∈ C.upper j := fun t h1 h2 =>
      ⟨C.mem_upper.mpr ⟨t, h1, h2, Or.inl rfl⟩, C.mem_upper.mpr ⟨t, h1, h2, Or.inr rfl⟩⟩
    by_cases hkj : k ≤ C.n - j
    · have e1 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).1 (hmem' (j + k) (by omega) (by omega)).1
        (sym2_ne_of_left (fun h => by have := C.inj_a _ (by omega) j hj h; omega) (C.ne_ab _ (by omega) j hj))
      have e2 := hbb _ _ (hmem' (j + i) (by omega) (by omega)).2 (hmem' (j + k) (by omega) (by omega)).2
        (sym2_ne_of_left (fun h => C.ne_ab j hj _ (by omega) h.symm)
          (fun h => by have := C.inj_b _ (by omega) j hj h; omega))
      rw [e1, e2]
      exact ⟨E.bonds_a_a (by omega) (by omega) (by omega), E.bonds_b_b (by omega) (by omega) (by omega)⟩
    · omega

omit [DecidableEq D] in
theorem ladderFrom_set {W : Type*} [Fintype W] [DecidableEq W] (N' : Molecule V W) (j : ℕ) (hj : j ≤ C.n)
    (hmem) (hrung) (hbb) (hdeg0) (hdeg) : (E.ladderFrom N' j hj hmem hrung hbb hdeg0 hdeg).set = C.upper j := by
  ext v
  rw [Ladder3.mem_set, C.mem_upper]
  change (∃ i ≤ C.n - j, v = C.a (j + i) ∨ v = C.b (j + i)) ↔ _
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨j + i, by omega, by omega, h⟩
  · rintro ⟨i, h1, h2, h⟩; exact ⟨i - j, by omega, by rwa [Nat.add_sub_cancel' h1]⟩

include E in
omit [DecidableEq D] in
/-- Bonds from an upper atom to the chain below `k + 1`: only the rails at `k + 1`. -/
theorem sum_low_a {k t : ℕ} (hk : k < C.n) (hkt : k < t) (ht : t ≤ C.n) :
    ∑ w ∈ (C.low k hk.le).set, M.bondsBetween (C.a t) w = if t = k + 1 then 1 else 0 := by
  classical
  have hzero : ∀ w ∈ (C.low k hk.le).set, w ≠ C.a k ∨ t ≠ k + 1 → M.bondsBetween (C.a t) w = 0 := by
    intro w hw hne
    have hwC := C.low_set_sub k hk.le hw
    obtain ⟨i, hi, hwi⟩ := (C.low k hk.le).mem_set.mp hw
    change i ≤ k at hi
    refine E.bonds_a_eq_zero ht hwC ?_ ?_
    · rw [Y2End.mem_nbA_iff]
      rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
      · rcases hwi with rfl | rfl
        · exact C.ne_ab i (by omega) t ht h
        · have := C.inj_b i (by omega) t ht h; omega
      · rcases hwi with rfl | rfl
        · have := C.inj_a i (by omega) (t - 1) (by omega) h
          rcases hne with h' | h'
          · exact h' (by rw [h]; congr 1; omega)
          · omega
        · exact C.ne_ab (t - 1) (by omega) i (by omega) h.symm
      · rcases hwi with rfl | rfl
        · have := C.inj_a i (by omega) (t + 1) (by omega) h; omega
        · exact C.ne_ab (t + 1) (by omega) i (by omega) h.symm
    · intro h; rcases hwi with rfl | rfl
      · have := C.inj_a t ht i (by omega) h; omega
      · exact C.ne_ab t ht i (by omega) h
  split_ifs with h
  · subst h
    have hak : C.a k ∈ (C.low k hk.le).set := (C.low k hk.le).a_mem le_rfl
    rw [sum_eq_single_of_mem (C.a k) hak (fun w hw hne => hzero w hw (Or.inl hne)),
      Degen.bondsBetween_comm]
    exact (C.rail k hk).1
  · exact sum_eq_zero fun w hw => hzero w hw (Or.inr h)

include E in
omit [DecidableEq D] in
theorem sum_low_b {k t : ℕ} (hk : k < C.n) (hkt : k < t) (ht : t ≤ C.n) :
    ∑ w ∈ (C.low k hk.le).set, M.bondsBetween (C.b t) w = if t = k + 1 then 1 else 0 := by
  have h := E.swap.sum_low_a (C := C.swap) hk hkt ht
  have hset : (C.swap.low k hk.le).set = (C.low k hk.le).set := by
    unfold YChain.set; exact union_comm _ _
  rw [hset] at h
  exact h

end Y2End
end WaveTurbulence.MoleProp4
