/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WKE.Taylor

/-! TARGET (wketaylor)–(wketaylor2), L752–755, at every time in a rescaled unit step. -/

public section
namespace WaveTurbulence.WKE
open MeasureTheory Set

/-- Every trilinear Taylor integrand is continuous on the whole real time axis. -/
theorem continuous_collision_taylorU {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → SchwartzMap (Mom d) ℝ) (δ : ℝ) (p a b c : ℕ) (k : Mom d) :
    Continuous (fun t => collisionOp (taylorU hd φ δ p a t)
      (taylorU hd φ δ p b t) (taylorU hd φ δ p c t) k) := by
  simp only [taylorU, collisionOp_smul_left, collisionOp_smul_mid, collisionOp_smul_right]
  fun_prop

/-- No small-step assumption is needed to make the finite Taylor recurrence integrable. -/
theorem intervalIntegrable_collision_taylorU {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → SchwartzMap (Mom d) ℝ) (δ : ℝ) (p a b c : ℕ) (k : Mom d) (t : ℝ) :
    IntervalIntegrable (fun t' => collisionOp (taylorU hd φ δ p a t')
      (taylorU hd φ δ p b t') (taylorU hd φ δ p c t') k) volume p t :=
  (continuous_collision_taylorU hd φ δ p a b c k).intervalIntegrable _ _

/-- Absolute convergence and identification with the source solution hold throughout a unit step. -/
theorem taylor_step_series {d : ℕ} (hd : 2 ≤ d)
    {φin : SchwartzMap (Mom d) ℝ} {T : ℝ} {φ : ℝ → SchwartzMap (Mom d) ℝ}
    (hφ : IsWKESolution φin T φ) {B : ℝ}
    (hB : ∀ τ ∈ Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hδB : δ ≤ taylorStep d B)
    {p : ℕ} (hp : ((p : ℝ) + 1) * δ ≤ T) {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom d) :
    Summable (fun n => |taylorU hd φ δ p n t k|) ∧
      ∑' n, taylorU hd φ δ p n t k = φ (δ * t) k := by
  let σ := δ * (t - p)
  have hσ0 : 0 ≤ σ := mul_nonneg hδ.le (sub_nonneg.mpr ht.1)
  have hσδ : σ ≤ δ := by dsimp [σ]; nlinarith [ht.2]
  have ha : 0 ≤ (p : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  have haT : (p : ℝ) * δ ∈ Icc 0 T := ⟨ha, by nlinarith⟩
  have hσsol : |σ| ≤ solTime (φ (p * δ)) := by
    rw [abs_of_nonneg hσ0]
    exact hσδ.trans (hδB.trans (taylorStep_le_solTime _ (hB _ haT)))
  have hs := summable_coeff_pointwise hd (φ (p * δ))
    (hσsol.trans (by linarith [solTime_pos (φ (p * δ))])) k
  constructor
  · simpa only [taylorU, smul_apply, smul_eq_mul, σ, Real.norm_eq_abs] using hs.norm
  · have heq := eq_taylorSol hd hφ hB ha hδ.le hδB (by nlinarith) σ ⟨hσ0, hσδ⟩
    have htime : (p : ℝ) * δ + σ = δ * t := by dsimp [σ]; ring
    rw [htime] at heq
    rw [heq, taylorSol_apply, clampT_of_mem _ ⟨hσ0, by rwa [abs_of_nonneg hσ0] at hσsol⟩]
    apply tsum_congr
    intro n
    rfl

end WaveTurbulence.WKE
