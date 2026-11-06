/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.UniformRegularCouple
/-! Sum estimates over the literal well-formed B2 code carrier. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Reg

/-- TARGET Proposition 4.4: finite code sum bounded using the proved exponential code count. -/
theorem norm_finsum_codes_le (n : ℕ) (f : RegCpl → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ Q, Q.wf = true → Q.size = 2 * n → ‖f Q‖ ≤ C) :
    ‖∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q‖ ≤
      ((12 ^ 9 : ℕ) ^ n : ℝ) * C := by
  classical
  letI := finite_coupleCodes n
  letI := Fintype.ofFinite {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  apply (norm_sum_le _ _).trans
  calc
    (∑ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}, ‖f Q.1‖) ≤
        ∑ _Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}, C :=
      Finset.sum_le_sum fun Q _ => hf Q.1 Q.2.1 Q.2.2
    _ = (Nat.card {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} : ℝ) * C := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ((12 ^ 9 : ℕ) ^ n : ℝ) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast coupleCodeCount_le_pow n

end WaveTurbulence.LGSpine
