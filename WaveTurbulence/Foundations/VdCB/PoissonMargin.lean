/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.TruncatedPoisson
public import WaveTurbulence.Foundations.VdCB.NonstationaryNegative
public import WaveTurbulence.Foundations.VdCB.FrequencyIntegration

/-!
# The adjustable margin in sharp truncated Poisson summation

After integer normalization of the derivative range, the usual cutoff
`α-η<ν<β+η` differs from `[0,N]` by at most two endpoint frequencies.
Their actual derivative distance is at least η, so their cost is explicit.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Frequencies retained by an adjustable open margin around the actual
normalized derivative range. -/
@[expose] noncomputable def marginFrequencies (α β η : ℝ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc 0 (N : ℤ)).filter (fun ν => α - η < ν ∧ (ν : ℝ) < β + η)

/-- For `η≤1`, the finite cutoff is exactly the usual open frequency window. -/
theorem mem_marginFrequencies_iff {α β η : ℝ} {N : ℕ} {ν : ℤ}
    (hα : 0 ≤ α) (hβ : β ≤ N) (hη : η ≤ 1) :
    ν ∈ marginFrequencies α β η N ↔ α - η < (ν : ℝ) ∧ (ν : ℝ) < β + η := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, h⟩
    · have hν : (-1 : ℝ) < ν := by linarith only [h.1, hα, hη]
      have hνZ : (-1 : ℤ) < ν := by exact_mod_cast hν
      omega
    · have hν : (ν : ℝ) < (N : ℝ) + 1 := by linarith only [h.2, hβ, hη]
      have hνZ : ν < (N : ℤ) + 1 := by exact_mod_cast hν
      omega

/-- Omitted margin frequencies consist of at most the two endpoint integers. -/
theorem marginFrequencies_compl_subset {α β η : ℝ} {N : ℕ}
    (hα : α < 1) (hβ : (N : ℝ) - 1 < β) (hη : 0 < η) :
    Finset.Icc 0 (N : ℤ) \ marginFrequencies α β η N ⊆ {0, (N : ℤ)} := by
  intro ν hν
  obtain ⟨hI, hS⟩ := Finset.mem_sdiff.mp hν
  obtain ⟨h0, hN⟩ := Finset.mem_Icc.mp hI
  have hbad : ¬(α - η < (ν : ℝ) ∧ (ν : ℝ) < β + η) := by
    intro h
    exact hS (Finset.mem_filter.mpr ⟨hI, h⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases not_and_or.mp hbad with h | h
  · left
    have hν1 : (ν : ℝ) < 1 := (not_lt.mp h).trans_lt (by linarith only [hα, hη])
    have hνZ : ν < (1 : ℤ) := by exact_mod_cast hν1
    omega
  · right
    have hνN : (N : ℝ) - 1 < (ν : ℝ) := by linarith only [not_lt.mp h, hβ, hη]
    have hνZ : (N : ℤ) - 1 < ν := by exact_mod_cast hνN
    omega

/-- Sharp van der Corput Poisson truncation with an adjustable margin.
This is the natural-number-endpoint version of Titchmarsh Lemma 4.7;
the explicit error is logarithmic in the derivative-range width plus
`2/(pi*η)`. Integer normalization is provided separately. -/
theorem norm_sum_sub_truncated_poisson_margin_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) {α β η : ℝ} (N : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : (N : ℝ) - 1 < β) (hβN : β ≤ N)
    (hη : 0 < η)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, α ≤ deriv f x ∧ deriv f x ≤ β)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ marginFrequencies α β η N, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
      ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        2 / (Real.pi * η) := by
  let S := marginFrequencies α β η N
  let T := Finset.Icc 0 (N : ℤ) \ S
  let I : ℤ → ℂ := fun ν => ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)
  have hS : S ⊆ Finset.Icc 0 (N : ℤ) := Finset.filter_subset _ _
  have htrunc := norm_sum_sub_truncated_poisson_le hf hab N
    (fun x hx => ⟨hα0.trans (hrange x hx).1, (hrange x hx).2.trans hβN⟩) hsecond
  have hd := hf.differentiable (by norm_num)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hterm (ν : ℤ) (hν : ν ∈ T) : ‖I ν‖ ≤ 1 / (Real.pi * η) := by
    obtain ⟨hI, hnot⟩ := Finset.mem_sdiff.mp hν
    have hbad : ¬(α - η < (ν : ℝ) ∧ (ν : ℝ) < β + η) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hI, h⟩)
    have hg : ContDiff ℝ 2 (fun x => f x - (ν : ℝ) * x) := hf.sub (contDiff_const.mul contDiff_id)
    have hg2 : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv (fun y => f y - (ν : ℝ) * y)) x := by
      simpa only [deriv_deriv_sub_frequency hf] using hsecond
    rcases not_and_or.mp hbad with h | h
    · apply norm_integral_expPhase_le_of_deriv_pos hg habR hη _ hg2
      intro x hx
      rw [deriv_sub_frequency hd]
      linarith only [not_lt.mp h, (hrange x hx).1]
    · apply norm_integral_expPhase_le_of_deriv_neg hg habR hη _ hg2
      intro x hx
      rw [deriv_sub_frequency hd]
      linarith only [not_lt.mp h, (hrange x hx).2]
  have hcard : T.card ≤ 2 := by
    have hh := Finset.card_le_card (marginFrequencies_compl_subset hα1 hβ0 hη)
    exact hh.trans Finset.card_le_two
  have htail : ‖∑ ν ∈ T, I ν‖ ≤ 2 / (Real.pi * η) := by
    calc
      _ ≤ ∑ ν ∈ T, ‖I ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ T, 1 / (Real.pi * η) := Finset.sum_le_sum hterm
      _ = (T.card : ℝ) / (Real.pi * η) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hsplit : (∑ ν ∈ Finset.Icc 0 (N : ℤ), I ν) = (∑ ν ∈ S, I ν) + ∑ ν ∈ T, I ν := by
    have hh := Finset.sum_sdiff hS (f := I)
    dsimp only [T]
    linear_combination -hh
  have heq : (∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) - (∑ ν ∈ S, I ν) =
      ((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        ∑ ν ∈ Finset.Icc 0 (N : ℤ), I ν) + ∑ ν ∈ T, I ν := by rw [hsplit]; ring
  change ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) - ∑ ν ∈ S, I ν‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add htrunc htail)

end WaveTurbulence.VdCB
