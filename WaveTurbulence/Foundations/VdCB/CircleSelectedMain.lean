/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleColumnCritical
public import WaveTurbulence.Foundations.VdCB.CircleColumnJetBounds
public import WaveTurbulence.Foundations.VdCB.CircleOctantFrequency
public import WaveTurbulence.Foundations.VdCB.CircleDualWindow

/-!
# The actual selected circle B-process main term

Every selected critical point is the explicit circle point. Reindexing
by actual dual frequencies puts the full main term into the proved
weighted circle A-estimate, including the arbitrary real center.
-/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The selected actual stationary main term is bounded at the transformed
circle scale. The critical equations and geometry are precisely the data
constructed by the generic B-process, not exponential-sum estimates. -/
theorem norm_circle_selected_main_le {R h U c a b r : ℝ} (hU : 1 ≤ U)
    (hUR : 3 * U ≤ R) (hh : 0 < h) (hr : 0 < r)
    (ha : R + c - 2 * U ≤ a) (hb : b ≤ R + c - U)
    (haOct : R + c - R * (1 - 1 / Real.sqrt 2) ≤ a) (hinner : a + r ≤ b - r)
    (m : ℤ) (N : ℕ) (z : ℤ → ℝ)
    (hrange : ∀ x ∈ Icc a b,
      0 ≤ -deriv (circleColumnExtension R h U (zero_lt_one.trans_le hU) c) x - m ∧
      -deriv (circleColumnExtension R h U (zero_lt_one.trans_le hU) c) x - m ≤ N)
    (hc : ∀ ν ∈ stationaryFrequencies
        (fun x => -circleColumnExtension R h U (zero_lt_one.trans_le hU) c x - (m : ℝ) * x) a b r N,
      a ≤ z ν - r ∧ z ν + r ≤ b ∧
        deriv (circleColumnExtension R h U (zero_lt_one.trans_le hU) c) (z ν) = -((m : ℝ) + ν)) :
    ‖∑ ν ∈ stationaryFrequencies
        (fun x => -circleColumnExtension R h U (zero_lt_one.trans_le hU) c x - (m : ℝ) * x) a b r N,
      expPhase (circleColumnExtension R h U (zero_lt_one.trans_le hU) c (z ν) +
        ((m : ℝ) + ν) * z ν - 1 / 8) /
      (Real.sqrt (-deriv (deriv (circleColumnExtension R h U (zero_lt_one.trans_le hU) c)) (z ν)) : ℂ)‖ ≤
      154618822665 * (h ^ ((11 : ℝ) / 30) * R ^ ((11 : ℝ) / 60) * U ^ ((7 : ℝ) / 20)) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  let F := circleColumnExtension R h U hU0 c
  let g : ℝ → ℝ := fun x => -F x - (m : ℝ) * x
  let S := stationaryFrequencies g a b r N
  have hF2 : ContDiff ℝ 2 F := (contDiff_circleColumnExtension hU0 hUR h c).of_le (by simp)
  have hneg2 : ContDiff ℝ 2 (fun x => -F x) := hF2.neg
  have hdneg := hneg2.differentiable (by norm_num)
  have hd (x : ℝ) : deriv g x = -deriv F x - m := by
    dsimp only [g]
    rw [deriv_sub_frequency hdneg, deriv.fun_neg]
  have hgrange : ∀ x ∈ Icc a b, 0 ≤ deriv g x ∧ deriv g x ≤ N := by simpa only [hd] using hrange
  let A := (m : ℝ) + deriv g (a + r)
  let B := (m : ℝ) + deriv g (b - r)
  have hset : S.image (fun ν => m + ν) = openFrequencies A B :=
    image_stationaryFrequencies_add_eq g a b r m N
      (hgrange (a + r) ⟨by linarith, by linarith⟩).1
      (hgrange (b - r) ⟨by linarith, by linarith⟩).2
  have hpoint (ν : ℤ) (hν : ν ∈ S) :
      R + c - z ν ∈ Icc U (2 * U) ∧ R + c - z ν ≤ R * (1 - 1 / Real.sqrt 2) := by
    obtain ⟨hal, hbu, _⟩ := hc ν hν
    constructor
    · exact column_interval_reflection_mem ha hb ⟨by linarith, by linarith⟩
    · linarith only [hal, haOct, hr]
  have hfirst (ν : ℤ) (hν : ν ∈ S) : circleSourceFirst R h (R + c - z ν) = ((m + ν : ℤ) : ℝ) := by
    have hcrit := (hc ν hν).2.2
    rw [deriv_circleColumnExtension hU0 hR (hpoint ν hν).1 hUR] at hcrit
    push_cast
    linarith only [hcrit]
  have hfreq : ∀ k ∈ openFrequencies A B,
      h ≤ (k : ℝ) ∧ R * h ^ 2 / (9 * U) ≤ (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ R * h ^ 2 / U := by
    intro k hk
    rw [← hset] at hk
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hu, hoct⟩ := hpoint ν hν
    have huarc : R + c - z ν ∈ Ioo 0 R := ⟨hU0.trans_le hu.1, by linarith [hu.2]⟩
    have hge := le_circleSourceFirst_of_octant hR hh huarc hoct
    have hs := circleSourceFirst_sq_bounds_of_octant (h := h) hU0 hUR hu hoct
    rw [hfirst ν hν] at hge hs
    refine ⟨hge, ?_, ?_⟩
    · convert hs.1 using 1; ring
    · convert hs.2 using 1; ring
  let P : ℤ → ℂ := fun k => (circleDualWeight R h k : ℂ) *
    expPhase (circleLatticeDualPhase R h k + c * (k : ℝ) - 1 / 8)
  have hterms : (∑ ν ∈ S, expPhase (F (z ν) + ((m : ℝ) + ν) * z ν - 1 / 8) /
      (Real.sqrt (-deriv (deriv F) (z ν)) : ℂ)) = ∑ ν ∈ S, P (m + ν) := by
    apply Finset.sum_congr rfl
    intro ν hν
    have hνpos : 0 < (m : ℝ) + ν := by
      have hge := (hfreq (m + ν) (hset ▸ Finset.mem_image.mpr ⟨ν, hν, rfl⟩)).1
      push_cast at hge
      exact hh.trans_le hge
    have heq := circleColumnExtension_stationary_main hU0 hUR hh hνpos (hpoint ν hν).1 (hc ν hν).2.2
    simpa only [P, Int.cast_add] using heq
  have hsum : (∑ ν ∈ S, P (m + ν)) = ∑ k ∈ openFrequencies A B, P k := by
    rw [← hset, Finset.sum_image]
    intro i _ j _ heq
    dsimp only at heq
    omega
  change ‖∑ ν ∈ S, expPhase (F (z ν) + ((m : ℝ) + ν) * z ν - 1 / 8) /
    (Real.sqrt (-deriv (deriv F) (z ν)) : ℂ)‖ ≤ _
  rw [hterms, hsum]
  simpa only [P, sub_eq_add_neg] using norm_sum_circleDualWindow_le hR hh hU c (-(1 / 8)) hfreq

end WaveTurbulence.VdCB
