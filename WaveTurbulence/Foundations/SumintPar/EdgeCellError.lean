/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SignedSums
import Mathlib.Tactic

/-!
# The scalar error bound for predecessor localization labels

The two alternative-variable cube errors cost at most two. The signed
input sums cost at most twice their coefficient mass. Since Λ≥1, the
resulting edge difference lies in a fixed interval of half-width 4Λ.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- Elementary quantitative localization of one predecessor difference. -/
theorem abs_edge_cell_error_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σk k a : ι → ℝ) (σe E C : κ → ℝ) (l lp b bp Λ : ℝ)
    (hrel : l - lp = (∑ i, σk i * k i) + ∑ c, σe c * E c)
    (hk : ∀ i, |2 * k i - a i| ≤ 1)
    (hE : ∀ c, |E c - C c| ≤ 1)
    (hl : |2 * l - b| ≤ 1) (hlp : |2 * lp - bp| ≤ 1)
    (hm : (∑ i, |σk i|) + ∑ c, |σe c| ≤ Λ) (hΛ : 1 ≤ Λ) :
    |b - bp - ((∑ i, σk i * a i) + 2 * ∑ c, σe c * C c)| ≤ 4 * Λ := by
  have hdk := sum_mul_difference σk k a 2
  have hde : (∑ c, σe c * (E c - C c)) = (∑ c, σe c * E c) - ∑ c, σe c * C c := by
    simpa only [one_mul] using sum_mul_difference σe E C 1
  have he : b - bp - ((∑ i, σk i * a i) + 2 * ∑ c, σe c * C c) =
      (∑ i, σk i * (2 * k i - a i)) + 2 * (∑ c, σe c * (E c - C c)) -
        (2 * l - b) + (2 * lp - bp) := by
    rw [hdk, hde]
    nlinarith only [hrel]
  have hkB : |∑ i, σk i * (2 * k i - a i)| ≤ ∑ i, |σk i| := by
    simpa only [mul_one] using abs_sum_mul_le σk (fun i => 2 * k i - a i) hk
  have heB : |∑ c, σe c * (E c - C c)| ≤ ∑ c, |σe c| := by
    simpa only [mul_one] using abs_sum_mul_le σe (fun c => E c - C c) hE
  rw [he]
  have htri :
      |(∑ i, σk i * (2 * k i - a i)) + 2 * (∑ c, σe c * (E c - C c)) -
        (2 * l - b) + (2 * lp - bp)| ≤
      |∑ i, σk i * (2 * k i - a i)| + 2 * |∑ c, σe c * (E c - C c)| +
        |2 * l - b| + |2 * lp - bp| := by
    calc
      _ ≤ |(∑ i, σk i * (2 * k i - a i)) + 2 * (∑ c, σe c * (E c - C c)) -
          (2 * l - b)| + |2 * lp - bp| := abs_add_le _ _
      _ ≤ (|(∑ i, σk i * (2 * k i - a i)) + 2 * (∑ c, σe c * (E c - C c))| +
          |2 * l - b|) + |2 * lp - bp| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by
        have hh := abs_add_le (∑ i, σk i * (2 * k i - a i)) (2 * ∑ c, σe c * (E c - C c))
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
        linarith
  have hkn : 0 ≤ ∑ i, |σk i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

end WaveTurbulence.SumintPar
