/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleSourceWindow
public import WaveTurbulence.Foundations.NumberTheory.MonotoneWeightedSums
import Mathlib.Tactic

/-!
# Circle source estimates on arbitrary closed integer windows

An integer translation reduces arbitrary endpoints to the shared natural
window interface. The first sample is retained with its exact unit cost.
Reflection then supplies the left cap with the same constant.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Actual closed integer-window circle estimate on the right octant. -/
theorem norm_sum_circleColumnPhase_Icc_le_BScale (A B : ℤ) {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h)
    (ha : R+c-2*U ≤ A) (hb : (B:ℝ) ≤ R+c-U) (haOct : c+R/Real.sqrt 2 ≤ A) :
    ‖∑ n ∈ Finset.Icc A B, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)-c))‖ ≤
      200000000000*VdCB.circleBScale R h U := by
  have hR : 1 ≤ R := by linarith only [hU,hUR]
  have hscale : 1 ≤ VdCB.circleBScale R h U := by
    unfold VdCB.circleBScale
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hh (by norm_num))
        (Real.one_le_rpow hR (by norm_num))) (Real.one_le_rpow hU (by norm_num))
  by_cases hAB : A ≤ B
  · let K : ℕ := (B-A).toNat
    have hKz : (K:ℤ) = B-A := Int.toNat_of_nonneg (by omega)
    have hKR : (K:ℝ) = (B:ℝ)-(A:ℝ) := by exact_mod_cast hKz
    have hsum := norm_sum_circleColumnPhase_le_BScale (c := c-(A:ℝ)) hU hUR hh
      (a := 0) (b := K) (Nat.zero_le K)
      (by norm_num only [Nat.cast_zero]; linarith only [ha])
      (by rw [hKR]; linarith only [hb])
      (by
        norm_num only [Nat.cast_zero]
        have he : R+(c-(A:ℝ))-R*(1-1/Real.sqrt 2) = c+R/Real.sqrt 2-(A:ℝ) := by ring
        rw [he]
        linarith only [haOct])
    have heq : (∑ n ∈ Finset.Ioc A B, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)-c))) =
        ∑ n ∈ Finset.Ico 0 K, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-(c-(A:ℝ)))) := by
      have he : B = A+(K:ℤ) := by omega
      rw [he,sum_Ioc_add_nat_eq_range]
      simp only [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro n _hn
      congr 2
      push_cast
      ring
    rw [← heq] at hsum
    rw [Finset.Icc_eq_cons_Ioc hAB,Finset.sum_cons]
    have he := (norm_add_le (expPhase (VdCB.circleColumnPhase R h ((A:ℝ)-c))) _).trans
      (add_le_add (le_of_eq (norm_expPhase (VdCB.circleColumnPhase R h ((A:ℝ)-c)))) hsum)
    linarith only [he,hscale]
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hAB),Finset.sum_empty,norm_zero]
    positivity

/-- Exact reflection of the original translated circle column sums. -/
theorem sum_circleColumnPhase_Icc_reflection (A B : ℤ) (R h c : ℝ) :
    (∑ n ∈ Finset.Icc A B, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)-c))) =
      ∑ n ∈ Finset.Icc (-B) (-A), expPhase (VdCB.circleColumnPhase R h ((n:ℝ)-(-c))) := by
  apply Finset.sum_bij (fun (n : ℤ) _ => -n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn m hm hnm
    omega
  · intro n hn
    refine ⟨-n,?_,by simp⟩
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n _hn
    unfold VdCB.circleColumnPhase
    push_cast
    congr 3
    ring

/-- The reflected left octant has the same actual closed-window estimate. -/
theorem norm_sum_circleColumnPhase_Icc_left_le_BScale (A B : ℤ) {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h)
    (ha : c-R+U ≤ A) (hb : (B:ℝ) ≤ c-R+2*U) (hbOct : (B:ℝ) ≤ c-R/Real.sqrt 2) :
    ‖∑ n ∈ Finset.Icc A B, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)-c))‖ ≤
      200000000000*VdCB.circleBScale R h U := by
  rw [sum_circleColumnPhase_Icc_reflection]
  apply norm_sum_circleColumnPhase_Icc_le_BScale (-B) (-A) hU hUR hh
  · push_cast; linarith only [hb]
  · push_cast; linarith only [ha]
  · push_cast; linarith only [hbOct]

end WaveTurbulence.NumberTheory
