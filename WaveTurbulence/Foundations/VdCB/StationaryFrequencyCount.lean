/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.StationaryFrequencies
public import WaveTurbulence.Foundations.VdCB.FiniteSums

/-!
# Counting the omitted endpoint frequencies

The complement of the actual central stationary range lies in two
short integer intervals. An upper curvature bound controls their widths.
-/

public section

open Set

namespace WaveTurbulence.VdCB

/-- The actual derivative values at the trimmed endpoints control the
number of frequencies omitted from the stationary sum. -/
theorem card_compl_stationaryFrequencies_le {f : ℝ → ℝ} {a b r H : ℝ} (N : ℕ)
    (hH : 0 ≤ H) (hleft : deriv f (a + r) ≤ H)
    (hright : (N : ℝ) - deriv f (b - r) ≤ H) :
    ((Finset.Icc 0 (N : ℤ) \ stationaryFrequencies f a b r N).card : ℝ) ≤ 2 * (H + 2) := by
  let L := integerInterval (-1) H
  let T := Finset.Icc 0 (N : ℤ) \ stationaryFrequencies f a b r N
  have hsub : T ⊆ L ∪ L.image (fun ν => (N : ℤ) - ν) := by
    intro ν hν
    obtain ⟨hνI, hνS⟩ := Finset.mem_sdiff.mp hν
    obtain ⟨hν0, hνN⟩ := Finset.mem_Icc.mp hνI
    have hbad : ¬(deriv f (a + r) < (ν : ℝ) ∧ (ν : ℝ) < deriv f (b - r)) := by
      intro h
      exact hνS (Finset.mem_filter.mpr ⟨hνI, h⟩)
    rcases not_and_or.mp hbad with h | h
    · apply Finset.mem_union_left
      apply mem_integerInterval.mpr
      have hν0R : (0 : ℝ) ≤ ν := by exact_mod_cast hν0
      exact ⟨by linarith only [hν0R], (not_lt.mp h).trans hleft⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(N : ℤ) - ν, ?_, ?_⟩
      · apply mem_integerInterval.mpr
        have hνNR : (ν : ℝ) ≤ N := by exact_mod_cast hνN
        have hh := not_lt.mp h
        push_cast
        constructor <;> linarith only [hνNR, hh, hright]
      · omega
  have hcard : T.card ≤ L.card + L.card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_image_le) L.card))
  have hcardR : (T.card : ℝ) ≤ (L.card : ℝ) + L.card := by exact_mod_cast hcard
  have hL : (L.card : ℝ) ≤ H + 2 := by
    have hh := card_integerInterval_le (show (-1 : ℝ) ≤ H by linarith)
    convert hh using 1; ring
  change (T.card : ℝ) ≤ _
  linarith only [hcardR, hL]

/-- An actual upper bound on the second derivative bounds the endpoint
frequency loss for a radius-trimmed stationary range. -/
theorem card_compl_stationaryFrequencies_le_of_curvature {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b r Λ : ℝ} (hr : 0 ≤ r) (hΛ : 0 ≤ Λ)
    (hinner : a + r ≤ b - r) (N : ℕ)
    (ha : deriv f a ≤ 1) (hb : (N : ℝ) - 1 ≤ deriv f b)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv f) x ≤ Λ) :
    ((Finset.Icc 0 (N : ℤ) \ stationaryFrequencies f a b r N).card : ℝ) ≤ 2 * (Λ * r + 3) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hsec := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => hcurv x (interior_subset hx))
  have hab : a ≤ b := by linarith
  have hl := hsec a (left_mem_Icc.mpr hab) (a + r) ⟨by linarith, by linarith⟩ (by linarith)
  have hu := hsec (b - r) ⟨by linarith, by linarith⟩ b (right_mem_Icc.mpr hab) (by linarith)
  have hh := card_compl_stationaryFrequencies_le N
    (show 0 ≤ 1 + Λ * r by positivity)
    (show deriv f (a + r) ≤ 1 + Λ * r by nlinarith only [hl, ha])
    (show (N : ℝ) - deriv f (b - r) ≤ 1 + Λ * r by nlinarith only [hu, hb])
  convert hh using 1
  ring

end WaveTurbulence.VdCB
