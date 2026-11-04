/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.ScaleAlgebra
public import WaveTurbulence.Foundations.Incoh.FactoredLinkMass

/-!
# The power cost of replacing a link

TARGET (incohproof18), (incohproof27). One trivial replacement costs
at most `L^(2γ+gain)` relative to the kinetic scale and incoherence weight.
This is uniform in the coupling for `0 < δ ≤ 1`.
-/

public section

namespace WaveTurbulence.Incoh

/-- An actual trivial lattice bound fits one weighted replacement penalty. -/
theorem trivial_link_le_weighted_penalty {d : ℕ} {L δ γ gain C C₂ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hgain : 0 ≤ gain)
    (hC : (5 : ℝ) ^ (2 * d) ≤ C) (hC₂ : 1 ≤ C₂) (p : Prop) [Decidable p] :
    (5 * L) ^ (2 * d) ≤
      (C * kineticLinkScale d γ δ L) * (if p then C₂ * L ^ (-gain) else 1) * L ^ (2 * γ + gain) := by
  have hLp := zero_lt_one.trans_le hL
  have hC₀ : 0 ≤ C := (pow_nonneg (by norm_num) _).trans hC
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ₁
  have hδi₀ : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hgain₁ : 1 ≤ L ^ gain := Real.one_le_rpow hL hgain
  have hbase₀ : 0 ≤ L ^ (2 * d) := by positivity
  have hcommon : (5 * L) ^ (2 * d) ≤ C * δ⁻¹ * L ^ (2 * d) := by
    rw [mul_pow]
    have hcoeff : (5 : ℝ) ^ (2 * d) ≤ C * δ⁻¹ := by
      exact hC.trans (le_mul_of_one_le_right hC₀ hδi)
    exact mul_le_mul_of_nonneg_right hcoeff hbase₀
  have hid₀ : kineticLinkScale d γ δ L * L ^ (2 * γ + gain) =
      δ⁻¹ * L ^ (2 * d) * L ^ gain := by
    unfold kineticLinkScale
    rw [mul_assoc, ← Real.rpow_add hLp, ← Real.rpow_natCast L (2 * d)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_assoc, ← Real.rpow_add hLp]
    congr 2
    ring
  have hid₁ : kineticLinkScale d γ δ L * L ^ (-gain) * L ^ (2 * γ + gain) =
      δ⁻¹ * L ^ (2 * d) := by
    unfold kineticLinkScale
    calc
      _ = δ⁻¹ * (L ^ (2 * ((d : ℝ) - γ)) * L ^ (-gain) * L ^ (2 * γ + gain)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hLp, ← Real.rpow_add hLp, ← Real.rpow_natCast L (2 * d)]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        congr 2
        ring
  by_cases hp : p
  · rw [ite_eq_left hp]
    have heq : (C * kineticLinkScale d γ δ L) * (C₂ * L ^ (-gain)) * L ^ (2 * γ + gain) =
        C₂ * (C * δ⁻¹ * L ^ (2 * d)) := by
      calc
        _ = C₂ * C * (kineticLinkScale d γ δ L * L ^ (-gain) * L ^ (2 * γ + gain)) := by ring
        _ = _ := by rw [hid₁]; ring
    rw [heq]
    exact hcommon.trans (le_mul_of_one_le_left (by positivity) hC₂)
  · rw [ite_eq_right hp, mul_one, mul_assoc, hid₀]
    calc
      _ ≤ (C * δ⁻¹ * L ^ (2 * d)) * L ^ gain :=
        hcommon.trans (le_mul_of_one_le_right (by positivity) hgain₁)
      _ = _ := by ring

/-- At most `k` replaced links cost at most `L^(dk)` in the source parameter range. -/
theorem replacement_loss_budget {d m k : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ≤ 1) (hη : 0 ≤ η) (hm : m ≤ k) :
    (2 * γ + incoherenceExponent d γ - η) * (m : ℝ) ≤ (d : ℝ) * k := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 2 * γ + incoherenceExponent d γ - η ≤ (d : ℝ) := by
    linarith [incoherenceExponent_le_one d γ]
  have hm' : (m : ℝ) ≤ k := by exact_mod_cast hm
  exact (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg m)).trans
    (mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg d))

end WaveTurbulence.Incoh
