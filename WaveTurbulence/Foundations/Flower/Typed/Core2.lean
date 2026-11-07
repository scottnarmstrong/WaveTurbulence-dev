/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Core1
/-! # FL-TYPED: the abstract profile estimate (weighted Leibniz with a gained support factor). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

theorem jbr_pos' (x : Mom d) : 0 < jbr x := Real.sqrt_pos.2 (by positivity)

theorem norm_le_jbr' (x : Mom d) : ‖x‖ ≤ jbr x := by
  unfold jbr
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

/-- The leading constant: the Leibniz sum of the unit-scale jets. -/
def S0Sum (Γ0 : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), (m.choose i : ℝ) * mulγ Γ0 Γ0 i

/-- The `z`-term constant. -/
def TSum (Γ0 Γv : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), (m.choose i : ℝ) *
    (mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i)

theorem term_bound {C a Z zc wf b0 gain : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hZ0 : 0 ≤ Z)
    (hwf : 0 ≤ wf) (hwf0 : wf ≤ b0) (hzc : 0 ≤ zc) (hgain : 0 ≤ gain)
    (hcase : Z = 0 ∨ (Z ≤ zc ∧ wf ≤ gain)) :
    C * ((a + Z) * wf) ≤ C * a * b0 + C * zc * gain := by
  rcases hcase with h | ⟨h1, h2⟩
  · subst h
    have : 0 ≤ C * zc * gain := mul_nonneg (mul_nonneg hC hzc) hgain
    have h3 : C * ((a + 0) * wf) ≤ C * a * b0 := by
      rw [add_zero, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hwf0 (mul_nonneg hC ha) |>.trans_eq' (by ring)
    linarith
  · have h3 : a * wf ≤ a * b0 := mul_le_mul_of_nonneg_left hwf0 ha
    have h4 : Z * wf ≤ zc * gain := mul_le_mul h1 h2 hwf hzc
    calc C * ((a + Z) * wf) = C * (a * wf + Z * wf) := by ring
      _ ≤ C * (a * b0 + zc * gain) := mul_le_mul_of_nonneg_left (by linarith) hC
      _ = _ := by ring

end WaveTurbulence.Flower.Typed
