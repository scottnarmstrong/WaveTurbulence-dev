/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
/-! TARGET L2065: transfer a root weight to an input leaf using the leaf count.
The leaf-count factor remains valid for a trivial tree (unlike the displayed 3*n factor). -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem jbr_le_card_mul_of_norm_le {d m : ℕ} (hm : 1 ≤ m) (x y : Mom d)
    (hnorm : ‖x‖ ≤ (m : ℝ) * ‖y‖) : jbr x ≤ (m : ℝ) * jbr y := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm)
  have hn : ‖x‖ ^ 2 ≤ (m : ℝ) ^ 2 * ‖y‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  have hj : jbr x ^ 2 ≤ ((m : ℝ) * jbr y) ^ 2 := by
    rw [jbr_sq, mul_pow, jbr_sq]
    nlinarith only [hm1, hn]
  exact (pow_le_pow_iff_left₀ (jbr_pos x).le (mul_nonneg (Nat.cast_nonneg m) (jbr_pos y).le)
    (by decide : (2 : ℕ) ≠ 0)).mp hj

theorem norm_units_zsmul {d : ℕ} (ε : ℤˣ) (x : Mom d) : ‖(ε : ℤ) • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

/-- Select a largest leaf once; its Japanese bracket controls the signed root sum. -/
theorem exists_jbr_sum_units_le_card_mul {ι : Type*} {d : ℕ} (s : Finset ι) (hs : s.Nonempty)
    (ε : ι → ℤˣ) (v : ι → Mom d) :
    ∃ i ∈ s, jbr (∑ j ∈ s, (ε j : ℤ) • v j) ≤ (s.card : ℝ) * jbr (v i) := by
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => ‖v j‖) hs
  refine ⟨i, hi, jbr_le_card_mul_of_norm_le (by simpa only [Nat.succ_le_iff] using card_pos.mpr hs) _ _ ?_⟩
  calc
    ‖∑ j ∈ s, (ε j : ℤ) • v j‖ ≤ ∑ j ∈ s, ‖(ε j : ℤ) • v j‖ := norm_sum_le _ _
    _ = ∑ j ∈ s, ‖v j‖ := sum_congr rfl fun j _ => norm_units_zsmul (ε j) (v j)
    _ ≤ ∑ _j ∈ s, ‖v i‖ := sum_le_sum fun j hj => hmax j hj
    _ = (s.card : ℝ) * ‖v i‖ := by simp

/-- The same selected leaf carries every natural root-weight power. -/
theorem exists_jbr_sum_units_pow_le {ι : Type*} {d : ℕ} (s : Finset ι) (hs : s.Nonempty)
    (ε : ι → ℤˣ) (v : ι → Mom d) (M : ℕ) :
    ∃ i ∈ s, jbr (∑ j ∈ s, (ε j : ℤ) • v j) ^ M ≤ (s.card : ℝ) ^ M * jbr (v i) ^ M := by
  obtain ⟨i, hi, h⟩ := exists_jbr_sum_units_le_card_mul s hs ε v
  exact ⟨i, hi, by simpa only [mul_pow] using pow_le_pow_left₀ (jbr_pos _).le h M⟩

end WaveTurbulence.LGSpine
