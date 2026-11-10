/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernel

/-! # Elementary facts on the time boxes `timeBox q q'`, `timeBoxGt q q'` (V5, hypotheses of the engine) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS3.FS Set

theorem timeBox_subset_cell (q q' : ℝ) : timeBox q q' ⊆ cell ![q, q'] := by
  intro ts hts i
  fin_cases i
  · exact hts.1
  · exact hts.2

theorem timeBoxGt_subset_cell (q q' : ℝ) : timeBoxGt q q' ⊆ cell ![q, q'] :=
  fun ts hts => timeBox_subset_cell q q' hts.1

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

end WaveTurbulence.VineEstS3
