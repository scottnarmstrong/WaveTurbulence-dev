/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorTerms
import Mathlib.Tactic

/-!
# Uniform source window geometry

The relation `τstar = Dsteps * δ` controls the rescaled difference of
any two enlarged input intervals by a fixed window depending on τstar.
Thus the Weyl constants can be chosen before δ and Dsteps, as required
by the exact prefix of sumint.
-/

@[expose] public section
set_option autoImplicit false

open Set

namespace WaveTurbulence.SumintPar

/-- Two source unit intervals enlarged by at most one have gap at most `Dsteps + 2`. -/
theorem enlarged_input_gap_le {D q p : ℕ} (hq : q < D) (hp : p < D)
    {c h s t : ℝ} (hh : h ≤ 1)
    (hs : s ∈ Icc ((q:ℝ)-c-h) ((q:ℝ)+1-c+h))
    (ht : t ∈ Icc ((p:ℝ)-c-h) ((p:ℝ)+1-c+h)) :
    |s-t| ≤ (D:ℝ)+2 := by
  have hq' : (q:ℝ)+1 ≤ D := by exact_mod_cast Nat.succ_le_of_lt hq
  have hp' : (p:ℝ)+1 ≤ D := by exact_mod_cast Nat.succ_le_of_lt hp
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith only [hs.1,hs.2,ht.1,ht.2,hh,hq',hp',hq0,hp0]

/-- The actual quadratic source time lies in a fixed Weyl window independent of δ and Dsteps. -/
theorem source_quadratic_window_le {D q p : ℕ} (hq : q < D) (hp : p < D)
    {L γ δ τstar c h s t : ℝ} (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hτ : τstar = (D:ℝ)*δ)
    (hh : h ≤ 1)
    (hs : s ∈ Icc ((q:ℝ)-c-h) ((q:ℝ)+1-c+h))
    (ht : t ∈ Icc ((p:ℝ)-c-h) ((p:ℝ)+1-c+h)) :
    |(16*sourceHalfScale L γ δ)*(s-t)| ≤
      (8*(τstar+2))*(4*L)^(2*γ) := by
  have hg := enlarged_input_gap_le hq hp hh hs ht
  have hτ0 : 0 ≤ τstar := by rw [hτ]; positivity
  have htime : δ*((D:ℝ)+2) ≤ τstar+2 := by rw [hτ]; nlinarith only [hδ1]
  have hscale : L^(2*γ) ≤ (4*L)^(2*γ) :=
    Real.rpow_le_rpow hL (by linarith) (by positivity)
  have hc : 0 ≤ 16*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  rw [abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ (16*sourceHalfScale L γ δ)*((D:ℝ)+2) := mul_le_mul_of_nonneg_left hg hc
    _ = 8*(δ*((D:ℝ)+2))*L^(2*γ) := by unfold sourceHalfScale; ring
    _ ≤ 8*(τstar+2)*L^(2*γ) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htime (by norm_num)) (Real.rpow_nonneg hL _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The enlarged source linear interval satisfies the landed short-window condition. -/
theorem source_linear_short_window {d : ℕ} {L γ η δ a b : ℝ}
    (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/16)
    (hγη : γ+η ≤ 1) (hab : a ≤ b) (hlen : b-a ≤ 3)
    (r : Mom d) (hr : ‖r‖ ≤ L^(-γ+η)) :
    ((4*sourceHalfScale L γ δ)*(b-a))*‖r‖ ≤ 4*L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc : 0 ≤ 4*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  calc
    _ ≤ ((4*sourceHalfScale L γ δ)*(b-a))*L^(-γ+η) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hc (sub_nonneg.mpr hab))
    _ ≤ ((4*sourceHalfScale L γ δ)*3)*L^(-γ+η) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hc) (Real.rpow_nonneg hLp.le _)
    _ = (6*δ)*L^(γ+η) := by
      unfold sourceHalfScale
      rw [show ((4*(δ*L^(2*γ)/2))*3)*L^(-γ+η) =
        (6*δ)*(L^(2*γ)*L^(-γ+η)) by ring, ← Real.rpow_add hLp]
      congr 2
      ring
    _ ≤ (6*δ)*L := by
      have hp : L^(γ+η) ≤ L := by simpa using Real.rpow_le_rpow_of_exponent_le hL hγη
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 4*L := mul_le_mul_of_nonneg_right (by linarith only [hδsmall]) hLp.le

/-- The two interval endpoints satisfy the exact contained-window premise
of the landed pair and normal estimates. The window depends only on τstar. -/
theorem source_enlarged_window_endpoints {N q p : ℕ} (hq : q < N) (hp : p < N)
    {L γ δ τstar c h : ℝ} (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hτ : τstar = (N:ℝ)*δ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    ∀ t ∈ Icc ((q:ℝ)-c-h) ((q:ℝ)+1-c+h),
      -((8*(τstar+2))*(4*L)^(2*γ)) ≤
        (16*sourceHalfScale L γ δ)*(((p:ℝ)-c-h)-t) ∧
      (16*sourceHalfScale L γ δ)*(((p:ℝ)+1-c+h)-t) ≤
        (8*(τstar+2))*(4*L)^(2*γ) := by
  intro t ht
  have hl : ((p:ℝ)-c-h) ∈ Icc ((p:ℝ)-c-h) ((p:ℝ)+1-c+h) :=
    ⟨le_rfl,by linarith only [hh0]⟩
  have hu : ((p:ℝ)+1-c+h) ∈ Icc ((p:ℝ)-c-h) ((p:ℝ)+1-c+h) :=
    ⟨by linarith only [hh0],le_rfl⟩
  exact ⟨(abs_le.mp (source_quadratic_window_le hp hq hL hγ hδ hδ1 hτ hh1 hl ht)).1,
    (abs_le.mp (source_quadratic_window_le hp hq hL hγ hδ hδ1 hτ hh1 hu ht)).2⟩

end WaveTurbulence.SumintPar
