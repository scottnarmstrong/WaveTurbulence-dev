/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.KernelM

/-!
# Kernel calculus for compositions of class `J` operators

* `KEqOn.kcomp`: composition respects equality on the triangle `0 ≤ s ≤ t ≤ 1`;
* `kcomp_finsetSum`: composition distributes over finite sums of continuous kernels;
* `JSym.continuous_kernel`: basic class `J` kernels are continuous;
* `kcomp_jsym_kernel`: Fubini, `J^{(1)} J^{(2)} = ∫∫ m^{(1)} m^{(2)} J_{ℓ₁;γ₁,γ₂} J_{ℓ₂;γ₃,γ₄}`
  (DH21 L968–L970);
* `kcomp_jker_split`: the decomposition `J = J' + J''` of DH21 L976–L1001, with the `χ₀` part
  written through `kerM` and the `χ_∞` part through `Φ = phiR`.
-/

public section

open MeasureTheory Set Complex Filter intervalIntegral
open scoped ContDiff Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

theorem norm_jker (ℓ γ₁ γ₂ t s : ℝ) : ‖jker ℓ γ₁ γ₂ t s‖ = 1 := by
  rw [jker, Complex.norm_exp]
  simp

theorem continuous_jker (ℓ γ₁ γ₂ : ℝ) : Continuous fun p : ℝ × ℝ => jker ℓ γ₁ γ₂ p.1 p.2 := by
  unfold jker; fun_prop

theorem continuous_jker_coeff (ℓ t s : ℝ) : Continuous fun γ : ℝ × ℝ => jker ℓ γ.1 γ.2 t s := by
  unfold jker; fun_prop

/-- Composition respects equality on the triangle. -/
theorem KEqOn.kcomp {K K' L L' : ℝ → ℝ → ℂ} (hK : KEqOn K K') (hL : KEqOn L L') :
    KEqOn (ClassJR.kcomp K L) (ClassJR.kcomp K' L') := by
  intro t s h0 hst ht1
  refine intervalIntegral.integral_congr fun z hz => ?_
  rw [Set.uIcc_of_le hst] at hz
  rw [hK t z (h0.trans hz.1) hz.2 ht1, hL z s h0 hz.1 (hz.2.trans ht1)]

/-- Composition distributes over finite sums of continuous kernels. -/
theorem kcomp_finsetSum {n₁ n₂ : ℕ} (K : Fin n₁ → ℝ → ℝ → ℂ) (L : Fin n₂ → ℝ → ℝ → ℂ)
    (hK : ∀ i, Continuous fun p : ℝ × ℝ => K i p.1 p.2)
    (hL : ∀ j, Continuous fun p : ℝ × ℝ => L j p.1 p.2) (t s : ℝ) :
    kcomp (fun t s => ∑ i, K i t s) (fun t s => ∑ j, L j t s) t s =
      ∑ i, ∑ j, kcomp (K i) (L j) t s := by
  have hc : ∀ i j, Continuous fun z => K i t z * L j z s := fun i j =>
    ((hK i).comp (continuous_const.prodMk continuous_id)).mul
      ((hL j).comp (continuous_id.prodMk continuous_const))
  simp only [kcomp]
  have : ∀ z, (∑ i, K i t z) * (∑ j, L j z s) = ∑ i, ∑ j, K i t z * L j z s := fun z => by
    rw [Finset.sum_mul_sum]
  simp_rw [this]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_finsetSum _ fun j _ => hc i j).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact intervalIntegral.integral_finsetSum fun j _ => (hc i j).intervalIntegrable _ _

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]

/-- Basic class `J` kernels are continuous in `(t, s)`. -/
theorem JSym.continuous_kernel (R : JSym ι) (hR : SymReg R.m) (α : ι → ℝ) :
    Continuous fun p : ℝ × ℝ => R.kernel α p.1 p.2 := by
  refine continuous_of_dominated (bound := fun γ => ‖R.m α γ‖) (fun p => ?_) (fun p => ?_)
    (hR.integrable α).norm (Eventually.of_forall fun γ => ?_)
  · exact (hR.integrable α).aestronglyMeasurable.mul
      (continuous_jker_coeff _ p.1 p.2).aestronglyMeasurable
  · exact Eventually.of_forall fun γ => by rw [norm_mul, norm_jker, mul_one]
  · exact continuous_const.mul ((continuous_jker (bundle R.y α) γ.1 γ.2))

/-- **Fubini for compositions of basic class `J` kernels** (DH21 L968–L970). -/
theorem kcomp_jsym_kernel (R₁ : JSym ι₁) (R₂ : JSym ι₂) (h₁ : SymReg R₁.m) (h₂ : SymReg R₂.m)
    (α₁ : ι₁ → ℝ) (α₂ : ι₂ → ℝ) {t s : ℝ} (hst : s ≤ t) :
    kcomp (R₁.kernel α₁) (R₂.kernel α₂) t s =
      ∫ p : (ℝ × ℝ) × (ℝ × ℝ), R₁.m α₁ p.1 * R₂.m α₂ p.2 *
        kcomp (jker (bundle R₁.y α₁) p.1.1 p.1.2) (jker (bundle R₂.y α₂) p.2.1 p.2.2) t s := by
  set ℓ₁ := bundle R₁.y α₁
  set ℓ₂ := bundle R₂.y α₂
  have hm : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => R₁.m α₁ p.1 * R₂.m α₂ p.2) := by
    rw [Measure.volume_eq_prod]
    exact (h₁.integrable α₁).mul_prod (h₂.integrable α₂)
  -- the integrand on `(z, p)`
  set F : ℝ → (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun z p =>
    R₁.m α₁ p.1 * R₂.m α₂ p.2 * (jker ℓ₁ p.1.1 p.1.2 t z * jker ℓ₂ p.2.1 p.2.2 z s) with hF
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioc s t)).prod volume) := by
    have hb : Integrable (fun q : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => ‖R₁.m α₁ q.2.1 * R₂.m α₂ q.2.2‖)
        ((volume.restrict (Ioc s t)).prod volume) :=
      ((integrable_const (1 : ℝ)).mul_prod hm.norm).congr (Eventually.of_forall fun q => by simp)
    refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
    · refine (hm.aestronglyMeasurable.comp_snd).mul ?_
      refine Continuous.aestronglyMeasurable ?_
      unfold jker; fun_prop
    · simp only [Function.uncurry, hF, norm_mul, norm_jker, mul_one]
      exact le_refl _
  calc kcomp (R₁.kernel α₁) (R₂.kernel α₂) t s
      = ∫ z in Ioc s t, ∫ p : (ℝ × ℝ) × (ℝ × ℝ), F z p := by
        rw [kcomp, intervalIntegral.integral_of_le hst]
        refine setIntegral_congr_fun measurableSet_Ioc fun z _ => ?_
        simp only [JSym.kernel, hF]
        have h := integral_prod_mul (μ := (volume : Measure (ℝ × ℝ)))
          (ν := (volume : Measure (ℝ × ℝ)))
          (fun γ : ℝ × ℝ => R₁.m α₁ γ * jker ℓ₁ γ.1 γ.2 t z)
          (fun γ : ℝ × ℝ => R₂.m α₂ γ * jker ℓ₂ γ.1 γ.2 z s)
        rw [← Measure.volume_eq_prod] at h
        rw [← h]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only
        ring
    _ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), ∫ z in Ioc s t, F z p := integral_integral_swap hFi
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hF, kcomp]
        rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le hst]

/-- Modulating a `J` kernel. -/
theorem jker_mul_exp (ℓ γ₁ γ₂ σ t s : ℝ) :
    jker ℓ γ₁ γ₂ t s * cexp (π * I * (σ * ((t - s : ℝ) : ℂ))) =
      jker ℓ (γ₁ + σ) (γ₂ - σ) t s := by
  rw [jker, jker, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The decomposition `J = J' + J''`** of DH21 L976–L1001: for `0 ≤ t - s ≤ 1`,
`J_{ℓ₁;γ₁,γ₂} J_{ℓ₂;γ₃,γ₄}` is the `χ₀` part `∫ kerM(x, q) J_{ℓ₁; γ₁+σ, γ₂+γ₃+γ₄-σ} dq` plus the
`χ_∞` part `Φ(x) (J_{ℓ₂; γ₁+γ₂+γ₃, γ₄} - J_{ℓ₁; γ₁, γ₂+γ₃+γ₄})`, with
`x = ℓ₂ - ℓ₁ + γ₂ + γ₃`. -/
theorem kcomp_jker_split (ℓ₁ γ₁ γ₂ ℓ₂ γ₃ γ₄ : ℝ) {t s : ℝ} (h0 : 0 ≤ t - s) (h1 : t - s ≤ 1) :
    kcomp (jker ℓ₁ γ₁ γ₂) (jker ℓ₂ γ₃ γ₄) t s =
      (∫ q : ℝ × ℝ, kerM (ℓ₂ - ℓ₁ + γ₂ + γ₃) q *
        jker ℓ₁ (γ₁ + q.1) (γ₂ + γ₃ + γ₄ - q.1) t s) +
      phiR (ℓ₂ - ℓ₁ + γ₂ + γ₃) * jker ℓ₂ (γ₁ + γ₂ + γ₃) γ₄ t s -
      phiR (ℓ₂ - ℓ₁ + γ₂ + γ₃) * jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s := by
  set x := ℓ₂ - ℓ₁ + γ₂ + γ₃
  rw [kcomp_jker]
  have hsplit : eInt x (t - s) = (chi0 x : ℂ) * eInt x (t - s) +
      (chiInfinity x : ℂ) * eInt x (t - s) := by
    rw [← add_mul, chiInfinity]
    push_cast
    ring
  rw [hsplit, mul_add, chiInfinity_mul_eInt, ← integral_kerM_mul_exp x ⟨h0, h1⟩,
    ← MeasureTheory.integral_const_mul]
  have h2 : jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s * cexp (π * I * (x * ((t - s : ℝ) : ℂ))) =
      jker ℓ₂ (γ₁ + γ₂ + γ₃) γ₄ t s := by
    rw [jker, jker, ← Complex.exp_add]
    congr 1
    simp only [x]
    push_cast
    ring
  rw [show jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s *
      (phiR x * (cexp (π * I * (x * ((t - s : ℝ) : ℂ))) - 1)) =
      phiR x * (jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s * cexp (π * I * (x * ((t - s : ℝ) : ℂ)))) -
        phiR x * jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s by ring, h2]
  rw [add_sub_assoc]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only
  rw [← jker_mul_exp]
  ring

end WaveTurbulence.ClassJR
