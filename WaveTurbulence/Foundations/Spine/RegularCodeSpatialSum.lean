/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RegularCodeSumBound
public import WaveTurbulence.Foundations.Spine.NormAssembly
/-! Full spatial-norm sums over the actual finite well-formed regular-couple code carrier. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset WaveTurbulence.Reg

 theorem SNorm_finsum_codes_le {d A B : ℕ} (hA : A ≠ 0) (n : ℕ)
    (f : RegCpl → Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ Q, Q.wf = true → Q.size = 2 * n → SNorm A B (f Q) ≤ ENNReal.ofReal C) :
    SNorm A B (fun x => ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q x) ≤
      ENNReal.ofReal (((12 ^ 9 : ℕ) ^ n : ℝ) * C) := by
  classical
  letI := finite_coupleCodes n
  letI := Fintype.ofFinite {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}
  have he : (fun x => ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q x) =
      fun x => ∑ Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}, f Q.1 x := by
    funext x
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  rw [he]
  apply (SNorm_finset_sum_bound univ (fun Q : {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} => f Q.1)
    (fun _ => C) (fun Q _ => contDiff_of_SNorm_bound hA _ C (hf Q.1 Q.2.1 Q.2.2))
      (fun _ _ => hC) (fun Q _ => hf Q.1 Q.2.1 Q.2.2)).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const, card_univ, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  have hcard := coupleCodeCount_le_pow n
  simpa only [Nat.card_eq_fintype_card] using (show
    (Nat.card {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} : ℝ) ≤ ((12 ^ 9 : ℕ) ^ n : ℝ) by exact_mod_cast hcard)

end WaveTurbulence.LGSpine
