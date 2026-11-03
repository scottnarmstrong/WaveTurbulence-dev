/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LargeCoordinate

/-! # Quantitative dominant-coordinate bounds for the independent strip -/

public section
namespace WaveTurbulence.CountLemmas

/-- The actual norm lower bound supplies a dominant coordinate with the
corresponding inverse coefficient bound. -/
theorem exists_strip_coordinate {d : ℕ} (hd : 0 < d) (r : Mom d)
    {P c : ℝ} (hP : 0 < P) (hc : 0 < c) (hr : c⁻¹*P ≤ ‖r‖) :
    ∃ i : Fin d, 0 < |r i| ∧ 1 ≤ ((d : ℝ)*c/P)*|r i| := by
  obtain ⟨i,hi⟩ := exists_large_coordinate hd r
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < c⁻¹*P := mul_pos (inv_pos.mpr hc) hP
  have hip : 0 < |r i| := (mul_pos_iff_of_pos_left hdp).mp (hpos.trans_le (hr.trans hi))
  refine ⟨i,hip,?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hP).mpr
  have hm := mul_le_mul_of_nonneg_left (hr.trans hi) hc.le
  have heq : c*(c⁻¹*P) = P := by field_simp
  rw [heq] at hm
  simpa only [one_mul] using hm.trans_eq (by ring)

/-- The retained strip coefficient can be replaced by a norm-scale lower
bound, without losing an additional power of the tolerance. -/
theorem inverse_strip_coefficient_le {L τ a D : ℝ}
    (hL : 0 ≤ L) (hτ : 0 ≤ τ) (ha : 0 < a) (hgap : 1 ≤ D*a) :
    2*τ*L/a+1 ≤ 2*D*τ*L+1 := by
  apply add_le_add ?_ le_rfl
  apply (div_le_iff₀ ha).mpr
  have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2*τ*L)
  nlinarith only [hm]

/-- When P is at least one lattice spacing, the same coordinate is
uniformly controlled by `d*c*L`, independently of P. -/
theorem strip_coordinate_lattice_gap {d : ℕ} {L P c : ℝ} (hL : 0 < L)
    (hP : L⁻¹ ≤ P) (hPp : 0 < P) (hc : 0 ≤ c) (i : Fin d) (r : Mom d)
    (hi : 1 ≤ ((d : ℝ)*c/P)*|r i|) :
    1 ≤ ((d : ℝ)*c*L)*|r i| := by
  have hinv : P⁻¹ ≤ L := (inv_le_comm₀ hPp hL).mpr hP
  have hm := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (d : ℝ)*c*|r i|)
  exact hi.trans (by convert hm using 1 <;> ring)

end WaveTurbulence.CountLemmas
