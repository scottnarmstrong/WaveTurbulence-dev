/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeadingProfile

/-! # Actual temporal L1 for the original leading approximation -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT WithLp

/-- Joint original energy/time L1 supplies the actual leading temporal density L1,
with no assumption on a singular limit or final spatial estimate. -/
theorem tree_integrable_approxApp_profile {d n : ℕ} (L δ γ : ℝ)
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hiC : Integrable (Function.uncurry C))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) :
    Integrable (fun lam => approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) W) := by
  have hmean (lam : ℝ × ℝ) :
      (∫ Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J}, C (ofLp Ω) lam) = ∫ β, C β lam :=
    (PiLp.volume_preserving_ofLp _).integral_comp
      (MeasurableEquiv.toLp 2 (({j : Fin n // j ∉ J}) → ℝ)).symm.measurableEmbedding
      (fun β => C β lam)
  unfold approxApp
  simp_rw [hmean]
  exact (hiC.integral_prod_right.const_mul _).mul_const _

end WaveTurbulence.RegAsymp
