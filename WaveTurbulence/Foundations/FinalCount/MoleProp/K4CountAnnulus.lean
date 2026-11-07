/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.AnnulusElementary
import Mathlib.Tactic

/-! # Large-radius planar fibers of the K4 count

The source large-M branch uses an actual local annulus estimate. The
energy center K is unrestricted; its positivity and the annulus radius
comparison are derived from the nonempty large-radius shell.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- A nonempty squared-radius shell separated from zero has a positive
energy center, and its true annulus radius is comparable to the retained
physical radius. -/
theorem k4_shell_radius_comparison (S : Finset (Fin 2 → ℤ)) (hne : S.Nonempty)
    (b : Mom 2) {M W K : ℝ} (hM : 0 < M) (_hW : 0 ≤ W) (hMW : 4*W ≤ M^2)
    (hs : ∀ n ∈ S, M ≤ ‖latticePoint 1 n-b‖ ∧
      |‖latticePoint 1 n-b‖^2-K| ≤ W) :
    0 < K ∧ M/2 ≤ Real.sqrt K ∧ W ≤ K/2 := by
  obtain ⟨n,hn⟩ := hne
  have hh := hs n hn
  have hsq : M^2 ≤ ‖latticePoint 1 n-b‖^2 := pow_le_pow_left₀ hM.le hh.1 2
  have hab := abs_le.mp hh.2
  have hK : 0 < K := by nlinarith only [hsq,hMW,hab.2,sq_pos_of_pos hM]
  refine ⟨hK,?_,?_⟩
  · have hsqrt := Real.sq_sqrt hK.le
    have hnon := Real.sqrt_nonneg K
    nlinarith only [hsq,hMW,hab.2,hsqrt,hnon,hM]
  · nlinarith only [hsq,hMW,hab.2]

/-- The source large-radius fiber is bounded by the actual local-annulus
majorant. This theorem retains its true Q=sqrt(K), avoiding any hidden
assumption on arbitrary spatial or energy centers. -/
theorem k4_large_shell_annulus_le (S : Finset (Fin 2 → ℤ)) (hne : S.Nonempty)
    (b a : Mom 2) {M W K B : ℝ} (hM : 0 < M) (hW : 1 ≤ W)
    (hMW : 4*W ≤ M^2) (hB : 0 ≤ B)
    (hs : ∀ n ∈ S, M ≤ ‖latticePoint 1 n-b‖ ∧
      |‖latticePoint 1 n-b‖^2-K| ≤ W)
    (hball : ∀ n ∈ S, ‖latticePoint 1 n-a‖ ≤ B) :
    (S.card : ℝ) ≤ 640000*(Real.sqrt W+B*W^((3 : ℝ)/2)/Real.sqrt K+
      B*Real.sqrt W*(Real.sqrt K)^(-((1 : ℝ)/3))) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  obtain ⟨hK,_hQ,hWK⟩ := k4_shell_radius_comparison S hne b hM hW0 hMW hs
  have hQ : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  let Q := Real.sqrt K
  let ρ := W/Q
  have hprod : Q*ρ=W := by
    dsimp only [ρ]
    calc
      Q*(W/Q) = W*(Q/Q) := by ring
      _ = W := by rw [div_self (show Q ≠ 0 from hQ.ne'),mul_one]
  have hρ : 0 ≤ ρ := div_nonneg hW0 hQ.le
  have hρQ : ρ ≤ Q/2 := by
    apply (div_le_iff₀ hQ).mpr
    dsimp only [Q]
    nlinarith only [Real.sq_sqrt hK.le,hWK]
  have hann : ∀ n ∈ S, |‖latticePoint 1 n-b‖-Q| ≤ ρ := by
    intro n hn
    have h := (hs n hn).2
    have he : (‖latticePoint 1 n-b‖-Q)*(‖latticePoint 1 n-b‖+Q) =
        ‖latticePoint 1 n-b‖^2-K := by
      dsimp only [Q]
      nlinarith only [Real.sq_sqrt hK.le]
    have hsum : 0 < ‖latticePoint 1 n-b‖+Q := add_pos_of_nonneg_of_pos (norm_nonneg _) hQ
    have hc : |‖latticePoint 1 n-b‖-Q| *(‖latticePoint 1 n-b‖+Q) ≤ W := by
      rw [← abs_of_pos hsum,← abs_mul,he]
      exact h
    have hm : |‖latticePoint 1 n-b‖-Q| *Q ≤
        |‖latticePoint 1 n-b‖-Q| *(‖latticePoint 1 n-b‖+Q) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg (latticePoint 1 n-b)))
        (abs_nonneg (‖latticePoint 1 n-b‖-Q))
    apply (le_div_iff₀ hQ).mpr
    nlinarith only [hc,hm]
  have hh := Counting.card_annulus_disc_le_expanded S b a hQ hρ hρQ
    (by rw [hprod]; exact hW) hB hann hball
  simpa only [hprod,Q] using hh

/-- A uniform radius-lower-bound version of the large-shell majorant,
retaining no energy-dependent constant in the final right-hand side. -/
theorem k4_large_shell_radius_le (S : Finset (Fin 2 → ℤ)) (hne : S.Nonempty)
    (b a : Mom 2) {M W K B : ℝ} (hM : 0 < M) (hW : 1 ≤ W)
    (hMW : 4*W ≤ M^2) (hB : 0 ≤ B)
    (hs : ∀ n ∈ S, M ≤ ‖latticePoint 1 n-b‖ ∧
      |‖latticePoint 1 n-b‖^2-K| ≤ W)
    (hball : ∀ n ∈ S, ‖latticePoint 1 n-a‖ ≤ B) :
    (S.card : ℝ) ≤ 640000*(Real.sqrt W+B*W^((3 : ℝ)/2)/(M/2)+
      B*Real.sqrt W*(M/2)^(-((1 : ℝ)/3))) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  obtain ⟨hK,hQ,_hWK⟩ := k4_shell_radius_comparison S hne b hM hW0 hMW hs
  have hMhalf : 0 < M/2 := by positivity
  have hterm : B*W^((3 : ℝ)/2)/Real.sqrt K ≤ B*W^((3 : ℝ)/2)/(M/2) :=
    div_le_div_of_nonneg_left (by positivity) hMhalf hQ
  have hpow := Real.rpow_le_rpow_of_nonpos hMhalf hQ (by norm_num : -((1 : ℝ)/3) ≤ 0)
  have ht := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ B*Real.sqrt W)
  have hh := k4_large_shell_annulus_le S hne b a hM hW hMW hB hs hball
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hterm,ht]) (by norm_num))

end WaveTurbulence.MoleProp
