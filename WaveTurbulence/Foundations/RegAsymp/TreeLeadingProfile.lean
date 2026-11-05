/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TimeCoefficientMass
public import WaveTurbulence.Foundations.ApproxNT.AppRep

/-! # Exact original time factor of the tree leading approximation -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp

/-- The original SRep zeroth mass implies actual joint energy/time integrability. -/
theorem tree_integrable_symbol_of_SRep {ι : Type} [Fintype ι] {θ a b A N : ℝ}
    (hθ : 0 ≤ θ) {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SRep θ a b A N C) :
    Integrable (Function.uncurry C) := by
  apply integrable_symbol_of_weighted_mass hC.reg hθ
  simpa only [dnorm_zero,gev,Nat.mul_zero,Nat.factorial_zero,pow_zero,Nat.cast_one,mul_one]
    using hC.norm 0

/-- Division by the actual constant leaf moment commutes with the inverse time profile. -/
theorem tree_pairedInverseProfile_div_const (A : (ℝ × ℝ) → ℂ) (c : ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => A lam/c) t = pairedInverseProfile A t/c := by
  unfold pairedInverseProfile
  simp only [div_eq_mul_inv]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

/-- Literal approxApp factors into the actual original integrated coefficient and
actual half-space singular integral. The energy-coordinate change has unit Jacobian. -/
theorem tree_paired_approxApp_eq_time_coefficient {d n : ℕ} (L δ γ : ℝ)
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hiC : Integrable (Function.uncurry C))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) W) t =
      (((L^(2*(d:ℝ)-2*γ)*δ⁻¹:ℝ):ℂ)^n * singInt J W) *
        (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1)) := by
  have hmean (lam : ℝ × ℝ) :
      (∫ Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J}, C (ofLp Ω) lam) = ∫ β, C β lam :=
    (PiLp.volume_preserving_ofLp _).integral_comp
      (MeasurableEquiv.toLp 2 (({j : Fin n // j ∉ J}) → ℝ)).symm.measurableEmbedding
      (fun β => C β lam)
  unfold approxApp
  simp_rw [hmean]
  calc
    _ = (((L^(2*(d:ℝ)-2*γ)*δ⁻¹:ℝ):ℂ)^n * singInt J W) *
        pairedInverseProfile (fun lam => ∫ β, C β lam) t := by
      unfold pairedInverseProfile
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _ = _ := by rw [← integral_integral_e2_eq_pairedProfile hiC t]

end WaveTurbulence.RegAsymp
