/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Transport
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YChain
import Mathlib.Tactic

/-! # Peeling a ladder of double bonds by operation (b)

A `Ladder3` is a sequence of double bonds `a i = b i` (`i ≤ m`) joined by single rails, whose first pair has both
atoms of degree three and whose other atoms have degree four, with no further bonds inside it. Operation (b)
(G6 `operation_b_normalized_bound`, DH23 Prop 10.1) removes the first pair at no cost in `𝔄`; the next pair then has
degree three. So `𝔄(N) ≤ 𝔄(N ∖ ladder)`. This is the "going from bottom to top" of DH23 L1952–L1956.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **A ladder of double bonds starting at a pair of degree-three atoms.** -/
structure Ladder3 (N : Molecule V D) where
  m : ℕ
  a : ℕ → V
  b : ℕ → V
  inj_a : ∀ i ≤ m, ∀ j ≤ m, a i = a j → i = j
  inj_b : ∀ i ≤ m, ∀ j ≤ m, b i = b j → i = j
  ne_ab : ∀ i ≤ m, ∀ j ≤ m, a i ≠ b j
  mem : ∀ i ≤ m, a i ∈ N.atoms ∧ b i ∈ N.atoms
  rung : ∀ i ≤ m, N.bondsBetween (a i) (b i) = 2
  rail : ∀ i < m, N.bondsBetween (a i) (a (i + 1)) = 1 ∧ N.bondsBetween (b i) (b (i + 1)) = 1
  deg0 : N.deg (a 0) = 3 ∧ N.deg (b 0) = 3
  deg4 : ∀ i, 0 < i → i ≤ m → N.deg (a i) = 4 ∧ N.deg (b i) = 4
  cross : ∀ i ≤ m, ∀ k < i, N.bondsBetween (a i) (b k) = 0 ∧ N.bondsBetween (b i) (a k) = 0
  long : ∀ i ≤ m, ∀ k, k + 1 < i → N.bondsBetween (a i) (a k) = 0 ∧ N.bondsBetween (b i) (b k) = 0

namespace Ladder3
variable {N : Molecule V D} (Lad : Ladder3 N)

/-- The atoms of the ladder. -/
def set : Finset V := (range (Lad.m + 1)).image Lad.a ∪ (range (Lad.m + 1)).image Lad.b

omit [DecidableEq D] in
theorem mem_set {v : V} : v ∈ Lad.set ↔ ∃ i ≤ Lad.m, v = Lad.a i ∨ v = Lad.b i := by
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
/-- Bonds of an atom outside `{a 0, b 0}` towards that pair. -/
theorem card_removed (v : V) (hv : v ∉ ({Lad.a 0, Lad.b 0} : Finset V)) :
    (Degen.removedDartsAt N {Lad.a 0, Lad.b 0} v).card = N.bondsBetween v (Lad.a 0) + N.bondsBetween v (Lad.b 0) := by
  have h := YChain.card_darts_toward (M := N) v {Lad.a 0, Lad.b 0} hv
  rw [sum_pair (Lad.ne_ab 0 (Nat.zero_le _) 0 (Nat.zero_le _))] at h
  exact h

omit [DecidableEq D] in
theorem a_notMem_pair {j : ℕ} (h1 : 0 < j) (h2 : j ≤ Lad.m) : Lad.a j ∉ ({Lad.a 0, Lad.b 0} : Finset V) := by
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨fun e => by have := Lad.inj_a j h2 0 (Nat.zero_le _) e; omega, Lad.ne_ab j h2 0 (Nat.zero_le _)⟩

omit [DecidableEq D] in
theorem b_notMem_pair {j : ℕ} (h1 : 0 < j) (h2 : j ≤ Lad.m) : Lad.b j ∉ ({Lad.a 0, Lad.b 0} : Finset V) := by
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨fun e => Lad.ne_ab 0 (Nat.zero_le _) j h2 e.symm,
    fun e => by have := Lad.inj_b j h2 0 (Nat.zero_le _) e; omega⟩

/-- **The ladder with its first pair removed.** -/
def shift (hm : 0 < Lad.m) : Ladder3 (Degen.eraseAtoms N {Lad.a 0, Lad.b 0}) where
  m := Lad.m - 1
  a i := Lad.a (i + 1)
  b i := Lad.b (i + 1)
  inj_a i hi j hj h := by have := Lad.inj_a (i + 1) (by omega) (j + 1) (by omega) h; omega
  inj_b i hi j hj h := by have := Lad.inj_b (i + 1) (by omega) (j + 1) (by omega) h; omega
  ne_ab i hi j hj := Lad.ne_ab (i + 1) (by omega) (j + 1) (by omega)
  mem i hi := by
    have h := Lad.mem (i + 1) (by omega)
    exact ⟨mem_sdiff.mpr ⟨h.1, Lad.a_notMem_pair (j := i + 1) (by omega) (by omega)⟩,
      mem_sdiff.mpr ⟨h.2, Lad.b_notMem_pair (j := i + 1) (by omega) (by omega)⟩⟩
  rung i hi := by
    rw [Degen.bondsBetween_erase_eq _ _ (Lad.a_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.b_notMem_pair (j := i + 1) (by omega) (by omega))]
    exact Lad.rung (i + 1) (by omega)
  rail i hi := by
    rw [Degen.bondsBetween_erase_eq _ _ (Lad.a_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.a_notMem_pair (j := i + 1 + 1) (by omega) (by omega)),
      Degen.bondsBetween_erase_eq _ _ (Lad.b_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.b_notMem_pair (j := i + 1 + 1) (by omega) (by omega))]
    exact Lad.rail (i + 1) (by omega)
  deg0 := by
    have hA := Lad.a_notMem_pair (j := 1) (by omega) hm
    have hB := Lad.b_notMem_pair (j := 1) (by omega) hm
    have ea := deg_eraseAtoms_add (N := N) _ hA
    have eb := deg_eraseAtoms_add (N := N) _ hB
    rw [Lad.card_removed _ hA] at ea
    rw [Lad.card_removed _ hB] at eb
    have r := Lad.rail 0 hm
    have c := Lad.cross 1 hm 0 (by omega)
    have d4 := Lad.deg4 1 (by omega) hm
    simp only [zero_add] at r ⊢
    rw [Degen.bondsBetween_comm N (Lad.a 0), Degen.bondsBetween_comm N (Lad.b 0)] at r
    omega
  deg4 i hi hi' := by
    have hA := Lad.a_notMem_pair (j := i + 1) (by omega) (by omega)
    have hB := Lad.b_notMem_pair (j := i + 1) (by omega) (by omega)
    have ea := deg_eraseAtoms_add (N := N) _ hA
    have eb := deg_eraseAtoms_add (N := N) _ hB
    rw [Lad.card_removed _ hA] at ea
    rw [Lad.card_removed _ hB] at eb
    have c := Lad.cross (i + 1) (by omega) 0 (by omega)
    have l := Lad.long (i + 1) (by omega) 0 (by omega)
    have d4 := Lad.deg4 (i + 1) (by omega) (by omega)
    omega
  cross i hi k hk := by
    rw [Degen.bondsBetween_erase_eq _ _ (Lad.a_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.b_notMem_pair (j := k + 1) (by omega) (by omega)),
      Degen.bondsBetween_erase_eq _ _ (Lad.b_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.a_notMem_pair (j := k + 1) (by omega) (by omega))]
    exact Lad.cross (i + 1) (by omega) (k + 1) (by omega)
  long i hi k hk := by
    rw [Degen.bondsBetween_erase_eq _ _ (Lad.a_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.a_notMem_pair (j := k + 1) (by omega) (by omega)),
      Degen.bondsBetween_erase_eq _ _ (Lad.b_notMem_pair (j := i + 1) (by omega) (by omega))
      (Lad.b_notMem_pair (j := k + 1) (by omega) (by omega))]
    exact Lad.long (i + 1) (by omega) (k + 1) (by omega)

theorem set_eq_shift (hm : 0 < Lad.m) : Lad.set = {Lad.a 0, Lad.b 0} ∪ (Lad.shift hm).set := by
  ext v
  rw [mem_union, Lad.mem_set, (Lad.shift hm).mem_set]
  simp only [mem_insert, mem_singleton]
  change (∃ i ≤ Lad.m, v = Lad.a i ∨ v = Lad.b i) ↔
    (v = Lad.a 0 ∨ v = Lad.b 0) ∨ ∃ i ≤ Lad.m - 1, v = Lad.a (i + 1) ∨ v = Lad.b (i + 1)
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Or.inl h
    · exact Or.inr ⟨i - 1, by omega, by rwa [Nat.sub_add_cancel hpos]⟩
  · rintro (h | ⟨i, hi, h⟩)
    · exact ⟨0, Nat.zero_le _, h⟩
    · exact ⟨i + 1, by omega, h⟩

omit [DecidableEq D] in
theorem set_zero (hm : Lad.m = 0) : Lad.set = {Lad.a 0, Lad.b 0} := by
  ext v
  rw [Lad.mem_set]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, hi, h⟩
    have : i = 0 := by omega
    subst this; exact h
  · intro h; exact ⟨0, Nat.zero_le _, h⟩

end Ladder3

/-- The erased admissibility of `lgAdm` is contained in `lgAdm` of the erased molecule. -/
theorem countAFree_erasedFree_le (N : Molecule V D) (Y : Finset V) {d : ℕ} (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    MoleProp.countAFree (Degen.eraseAtoms N Y) L γ δ C1 (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility N Y (lgAdm N L γ η P)) P ≤
      AFree (Degen.eraseAtoms N Y) d L γ δ η C1 P := by
  unfold AFree MoleProp.countAFree
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono (MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
    obtain ⟨κ0, ⟨hLG, hC⟩, _, rfl⟩ := h
    exact ⟨MoleProp.largeGap_erase N L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase N L 0 _ P _ hC⟩)) bot_le

theorem nonneg_erase {N : Molecule V D} {P : Finset V → ℝ} (hP : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S)
    (Y : Finset V) : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms N Y), 0 ≤ P S := fun S hS => by
  classical
  have := (MoleProp.isLadderCell_erase_iff N Y S).mp (mem_filter.mp hS).2
  exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩)

/-- **Peeling a `Ladder3` by operation (b)**: `𝔄(N) ≤ 𝔄(N ∖ ladder)`. -/
theorem ladder_peel (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D), N.IsMolecule →
      ∀ Lad : Ladder3 N, ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        AFree N d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms N Lad.set) d L γ δ η C1 P := by
  obtain ⟨Cstar, hCstar, hB⟩ := MoleProp.operation_b_normalized_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hB C1 hC1 δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hN Lad P hP
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  -- one step of operation (b)
  have step : ∀ {D : Type _} [Fintype D] [DecidableEq D] (N : Molecule V D), N.IsMolecule →
      ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, a ≠ b → N.deg a = 3 → N.deg b = 3 → N.bondsBetween a b = 2 →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        AFree N d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms N {a, b}) d L γ δ η C1 P := by
    intro D _ _ N hN a ha b hb hab h3a h3b h2 P hP
    exact (hR L hLR hlog N hN a ha b hb hab h3a (Or.inl h3b) h2 (lgAdm N L γ η P) P (fun κ h => h.1)
      (fun κ h => h.2) hP).trans (countAFree_erasedFree_le N {a, b} L γ δ η C1 P)
  -- induction on the length
  have key : ∀ k : ℕ, ∀ {D : Type _} [Fintype D] [DecidableEq D] (N : Molecule V D), N.IsMolecule →
      ∀ Lad : Ladder3 N, Lad.m = k → ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        AFree N d L γ δ η C1 P ≤ AFree (Degen.eraseAtoms N Lad.set) d L γ δ η C1 P := by
    intro k
    induction k with
    | zero =>
      intro D _ _ N hN Lad hk P hP
      rw [Lad.set_zero hk]
      exact step N hN _ (Lad.mem 0 (Nat.zero_le _)).1 _ (Lad.mem 0 (Nat.zero_le _)).2
        (Lad.ne_ab 0 (Nat.zero_le _) 0 (Nat.zero_le _)) Lad.deg0.1 Lad.deg0.2 (Lad.rung 0 (Nat.zero_le _)) P hP
    | succ k ih =>
      intro D _ _ N hN Lad hk P hP
      have hm : 0 < Lad.m := by omega
      have h1 := step N hN _ (Lad.mem 0 (Nat.zero_le _)).1 _ (Lad.mem 0 (Nat.zero_le _)).2
        (Lad.ne_ab 0 (Nat.zero_le _) 0 (Nat.zero_le _)) Lad.deg0.1 Lad.deg0.2 (Lad.rung 0 (Nat.zero_le _)) P hP
      have h2 := ih (Degen.eraseAtoms N {Lad.a 0, Lad.b 0}) (Degen.isMolecule_eraseAtoms N hN _) (Lad.shift hm)
        (by change Lad.m - 1 = k; omega) P (nonneg_erase hP _)
      rw [Lad.set_eq_shift hm]
      exact h1.trans (h2.trans (afree_erase_erase_le N _ _ L γ δ η C1 P))
  exact key Lad.m N hN Lad rfl P hP

end WaveTurbulence.MoleProp4
