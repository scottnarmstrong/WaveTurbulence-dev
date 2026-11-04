/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep

/-! # Derivative-free size bound for the leading NT cell term -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset

/-- The leading cell term uses only the literal symbol L1 mass. -/
theorem exists_app_cell_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      ∀ (J : Finset ι) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ μ : ℝ, 0 < μ → ∀ p q ξ η : ι → Mom d,
      ‖(μ⁻¹:ℂ)^Fintype.card ι*(∫ Ω, Ψ Ω)*∏ j, cellOp J j (p j) (q j) (ξ j) (η j)‖ ≤
        (K/μ)^Fintype.card ι*D0 := by
  obtain ⟨K,hK,hb⟩ := exists_cellOp_bound hd
  refine ⟨K,hK,?_⟩
  intro ι _ _ J Ψ D0 hΨ μ hμ p q ξ η
  have hμi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ.le
  have hD0 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hΨ
  have hnorm : ‖∫ Ω, Ψ Ω‖ ≤ D0 := (norm_integral_le_integral_norm _).trans hΨ
  have hp : ‖∏ j, cellOp J j (p j) (q j) (ξ j) (η j)‖ ≤ K^Fintype.card ι := by
    apply (Finset.norm_prod_le _ _).trans
    calc
      _ ≤ ∏ _j : ι, K := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb J j _ _ _ _)
      _ = _ := by simp
  rw [norm_mul,norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hμ]
  calc
    _ ≤ (μ⁻¹)^Fintype.card ι*D0*K^Fintype.card ι :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_eq_mul_inv,mul_pow]; ring

end WaveTurbulence.RegAsymp
