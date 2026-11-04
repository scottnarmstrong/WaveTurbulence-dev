/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreCrude

/-!
# The total fixed-time counting loss affects at most eight inputs

The source gap/time-volume constant may depend on the fixed number of
steps. Its exponent is at most eight, independently of the packet size.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual mixed mass of one core is bounded by one counting base to its literal arity. -/
theorem lintegral_sourceCore_fixed_count_pow_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : ‖r‖ ≤ 1)
    (t c : ℝ) {h : ℝ} (hh : h ≤ 1) (b : FactorIdx D.S) (s : Set D.S.TVar) (x : D.S.TVar → ℝ) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure s x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
      (ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d))^(sourceCoreArity D b) := by
  have he := lintegral_sourceCore_fixed_count_le D hD hL hη δ p ν r hr t c hh b s x
  apply he.trans_eq
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [mul_pow,mul_pow,pow_mul]
  ring

/-- Fixing at most two native times incurs a counting loss with total exponent at most eight. -/
theorem prod_touchedCore_fixed_count_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 1 ≤ L) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (hr : ‖r‖ ≤ 1)
    (t c : ℝ) {h : ℝ} (hh : h ≤ 1) (s : Finset D.S.TVar) (hs : s.card ≤ 2) (x : D.S.TVar → ℝ) :
    (∏ b ∈ sourceExitCores D s, ∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure (s:Set D.S.TVar) x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
      (ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d))^8 := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hQ : 1 ≤ (8*L+1)^d := one_le_pow₀ (by linarith only [hL])
  have hK : 1 ≤ max 1 (((N:ℝ)+2)^(1-3*η)) := le_max_left _ _
  have hbase : 1 ≤ ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [hQ,hK]
  calc
    _ ≤ ∏ b ∈ sourceExitCores D s,
        (ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d))^(sourceCoreArity D b) :=
      Finset.prod_le_prod (fun b _ => lintegral_sourceCore_fixed_count_pow_le D hD hLp hη δ p ν r hr t c hh b _ x)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_right₀ hbase (sum_arity_sourceExitCores_le_eight D s hs)

end WaveTurbulence.Sumint
