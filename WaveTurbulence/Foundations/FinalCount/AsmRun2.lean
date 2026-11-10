/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmLabel
public import WaveTurbulence.Foundations.FinalCount.AsmRun3
/-! **FINALCOUNT-ASSEMBLY, M7 (phase 2): existence of the triangle phase.**  An eligible triangle admits a step `HStep2C`
(labels by `exists_label_of_SG`, `kp` by `IotaHit`, `PClosed T.kept (triKeep s T)` from `Inv.ab`: an already cut atom has degree `2`
so its ghost has no darts, `3 ≤ deg` of the `ε` atoms from `Flat`).  The number of darts strictly decreases. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} {R : ℕ}

theorem tri_m3_atom_f {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M) (y : D) (j : Fin 3)
    (h : T.m3.atom y = T.f j) : M.atom y = T.t j ∧ y ≠ T.a j ∧ y ≠ T.b j := by
  by_cases hex : ∃ i, M.atom y = T.t i
  · obtain ⟨i, hi⟩ := hex
    by_cases hy : y = T.a i ∨ y = T.b i
    · exfalso
      rw [T.m3_atom_tri y i hy] at h
      exact T.f_fresh j (h ▸ T.t_mem i)
    · push Not at hy
      have := T.m3_atom_moved y i hi hy.1 hy.2
      rw [this] at h
      have : i = j := T.f_inj h
      subst this
      exact ⟨hi, hy.1, hy.2⟩
  · push Not at hex
    rw [T.m3_atom_other y hex] at h
    exact absurd (h ▸ M.atom_mem y) (T.f_fresh j)

theorem tri_keep_closed {s : St.{u} V D₀} {R : ℕ} (hI : Inv R s) (T : TriData s.M) :
    PClosed T.kept (triKeep s T) := by
  intro x _ j hj hcon
  have hcon' : T.m3.atom (s.M.mate x.1) = T.f j := hcon
  obtain ⟨h1, h2, h3⟩ := tri_m3_atom_f T _ j hcon'
  have hab := hI.ab (T.t j) (T.t_mem j) hj
  have hsub : ({T.a j, T.b j, s.M.mate x.1} : Finset s.D) ⊆ s.M.dartsAt (T.t j) := by
    intro z hz
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact T.atom_a j
    · exact T.atom_b j
    · exact h1
  have hne1 : T.a j ≠ T.b j := fun e => by
    have := T.out_a j; rw [e, T.out_b j] at this; exact absurd this (by simp)
  have hcard : ({T.a j, T.b j, s.M.mate x.1} : Finset s.D).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨T.a j, T.b j, s.M.mate x.1, hne1, fun e => h2 e.symm, fun e => h3 e.symm, rfl⟩
  have := Finset.card_le_card hsub
  have hd : s.M.deg (T.t j) = (s.M.dartsAt (T.t j)).card := rfl
  omega

theorem card_dart_triSt_lt {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep s T)) :
    Fintype.card (triSt s T Q kp hcl).D < Fintype.card s.D := by
  show Fintype.card (PDart T.kept (triKeep s T)) < Fintype.card s.D
  refine lt_of_le_of_lt (Fintype.card_subtype_le _) ?_
  show Fintype.card (PDart T.m3 T.TP) < Fintype.card s.D
  refine Fintype.card_subtype_lt (x := T.a 0) ?_
  intro hP
  exact hP 0 (T.m3_atom_tri _ 0 (Or.inl rfl))

end WaveTurbulence.FinalCountAsm
