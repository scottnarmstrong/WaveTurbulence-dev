/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSup2
public import WaveTurbulence.Foundations.Stage1.Represents.RepApp1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: slot-level superpositions from the gate norms

Elementary facts on the time boxes (copied from `VineEstS3.BoxFacts`, whose imports clash with the spine) and the
passage from `XNormRestr` bounds of a continuous slot kernel to `CenSup` / `Sup`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic Set
open scoped ENNReal

theorem timeBox_subset_cell (q q' : ℝ) : timeBox q q' ⊆ cell ![q, q'] := by
  intro ts hts i
  fin_cases i
  · exact hts.1
  · exact hts.2

theorem timeBoxGt_subset_cell (q q' : ℝ) : timeBoxGt q q' ⊆ cell ![q, q'] :=
  fun ts hts => timeBox_subset_cell q q' hts.1

theorem timeBox_eq_pi (q q' : ℝ) :
    timeBox q q' = {ts | ts 0 ∈ Icc q (q + 1)} ∩ {ts | ts 1 ∈ Icc q' (q' + 1)} := rfl

theorem convex_timeBox (q q' : ℝ) : Convex ℝ (timeBox q q') := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have := (convex_Icc q (q + 1)) hx.1 hy.1 ha hb hab
    simpa using this
  · have := (convex_Icc q' (q' + 1)) hx.2 hy.2 ha hb hab
    simpa using this

theorem convex_timeBoxGt (q q' : ℝ) : Convex ℝ (timeBoxGt q q') := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_timeBox q q' hx.1 hy.1 ha hb hab, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := hx.2
  have h2 := hy.2
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simpa using h2
  · rcases hb.eq_or_lt with rfl | hb'
    · have : a = 1 := by linarith
      subst this; simpa using h1
    · nlinarith

theorem timeBox_subset_closure_interior (q q' : ℝ) : timeBox q q' ⊆ closure (interior (timeBox q q')) := by
  have hne : (interior (timeBox q q')).Nonempty := by
    refine ⟨![q + 1/2, q' + 1/2], ?_⟩
    rw [mem_interior]
    refine ⟨{ts | q < ts 0 ∧ ts 0 < q + 1} ∩ {ts | q' < ts 1 ∧ ts 1 < q' + 1}, ?_, ?_, ?_⟩
    · intro ts hts; exact ⟨⟨hts.1.1.le, hts.1.2.le⟩, ⟨hts.2.1.le, hts.2.2.le⟩⟩
    · refine IsOpen.inter ?_ ?_
      · exact (isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)
      · exact (isOpen_lt continuous_const (continuous_apply 1)).inter (isOpen_lt (continuous_apply 1) continuous_const)
    · simp only [mem_inter_iff, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [(convex_timeBox q q').closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

theorem timeBoxGt_subset_closure_interior {q q' : ℝ} (h : q' ≤ q) :
    timeBoxGt q q' ⊆ closure (interior (timeBoxGt q q')) := by
  have hne : (interior (timeBoxGt q q')).Nonempty := by
    refine ⟨![q + 3/4, q' + 1/4], ?_⟩
    rw [mem_interior]
    refine ⟨{ts | q < ts 0 ∧ ts 0 < q + 1} ∩ {ts | q' < ts 1 ∧ ts 1 < q' + 1} ∩ {ts | ts 1 < ts 0}, ?_, ?_, ?_⟩
    · intro ts hts; exact ⟨⟨⟨hts.1.1.1.le, hts.1.1.2.le⟩, ⟨hts.1.2.1.le, hts.1.2.2.le⟩⟩, hts.2⟩
    · refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
      · exact (isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)
      · exact (isOpen_lt continuous_const (continuous_apply 1)).inter (isOpen_lt (continuous_apply 1) continuous_const)
      · exact isOpen_lt (continuous_apply 1) (continuous_apply 0)
    · simp only [mem_inter_iff, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by linarith⟩
  rw [(convex_timeBoxGt q q').closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure


open Classical in
/-- The explicit constant of the couple superposition (depends only on `d` and `η`). -/
noncomputable def cenCplC (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ d ∧ 0 ≤ η then
    (exists_cenSup (r := 2) (d := d) h.1 h.2 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega) (by omega)).choose
  else 0

open Classical in
/-- The explicit constant of the tree superposition (depends only on `d` and `η`). -/
noncomputable def supTreeC (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ d ∧ 0 ≤ η then
    (exists_sup (r := 2) (d := d) h.2 (Λ₁ := 30 * d) (by have := h.1; omega)).choose
  else 0

theorem cenCplC_spec (d : ℕ) (η : ℝ) (hd : 1 ≤ d) (hη0 : 0 ≤ η) :
    cenCplC d η ≠ ⊤ ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom d → ℂ) (X : ℝ≥0∞), X ≠ ⊤ →
      (∀ k, Continuous fun t => f t k) →
      XNormRestr η (30 * d) (30 * d) (timeBox (q : ℝ) q') Set.univ f ≤ X →
      CenSup (30 * d) (timeBox (q : ℝ) q') f (cenCplC d η * X) := by
  have hh : 1 ≤ d ∧ 0 ≤ η := ⟨hd, hη0⟩
  obtain ⟨hC, h⟩ := (exists_cenSup (r := 2) (d := d) hd hη0 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega)
    (by omega)).choose_spec
  have e : cenCplC d η = (exists_cenSup (r := 2) (d := d) hd hη0 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega)
    (by omega)).choose := by
    unfold cenCplC; simp only [hh, and_self, ↓reduceDIte]
  rw [e]
  exact ⟨hC, fun q q' f X hX hfc hn => h ![(q : ℝ), q'] _ f X hX (timeBox_subset_cell _ _)
    (timeBox_subset_closure_interior _ _) hfc hn⟩

theorem supTreeC_spec (d : ℕ) (η : ℝ) (hd : 1 ≤ d) (hη0 : 0 ≤ η) :
    supTreeC d η ≠ ⊤ ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom d → ℂ) (X : ℝ≥0∞), X ≠ ⊤ → q' ≤ q →
      (∀ k, Continuous fun t => f t k) →
      XNormRestr η (30 * d) 0 (timeBoxGt (q : ℝ) q') Set.univ f ≤ X →
      Sup (30 * d) (timeBoxGt (q : ℝ) q') f (supTreeC d η * X) := by
  have hh : 1 ≤ d ∧ 0 ≤ η := ⟨hd, hη0⟩
  obtain ⟨hC, h⟩ := (exists_sup (r := 2) (d := d) hη0 (Λ₁ := 30 * d) (by omega)).choose_spec
  have e : supTreeC d η = (exists_sup (r := 2) (d := d) hη0 (Λ₁ := 30 * d) (by omega)).choose := by
    unfold supTreeC; simp only [hh, and_self, ↓reduceDIte]
  rw [e]
  exact ⟨hC, fun q q' f X hX hqq hfc hn => h ![(q : ℝ), q'] _ f X hX (timeBoxGt_subset_cell _ _)
    (timeBoxGt_subset_closure_interior (by exact_mod_cast hqq)) hfc hn⟩

theorem cenSup_couple (P : WTParams) (hd : 1 ≤ P.d) (hη0 : 0 ≤ P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = cenCplC P.d P.η ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞),
      X ≠ ⊤ → (∀ k, Continuous fun t => f t k) →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ f ≤ X →
      CenSup (30 * P.d) (timeBox (q : ℝ) q') f (C * X) := by
  obtain ⟨hC, h⟩ := cenCplC_spec P.d P.η hd hη0
  exact ⟨_, hC, rfl, h⟩

theorem sup_tree (P : WTParams) (hd : 1 ≤ P.d) (hη0 : 0 ≤ P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = supTreeC P.d P.η ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞),
      X ≠ ⊤ → q' ≤ q → (∀ k, Continuous fun t => f t k) →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt (q : ℝ) q') Set.univ f ≤ X →
      Sup (30 * P.d) (timeBoxGt (q : ℝ) q') f (C * X) := by
  obtain ⟨hC, h⟩ := supTreeC_spec P.d P.η hd hη0
  exact ⟨_, hC, rfl, h⟩

end WaveTurbulence.Represents
