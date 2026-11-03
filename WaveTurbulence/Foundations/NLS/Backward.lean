/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkMass
public import WaveTurbulence.Foundations.NLS.SpaceTimeSeries
public import WaveTurbulence.Foundations.NLS.Symmetry

/-!
# The first reduction, backward direction: from the `a`-system to smooth NLS solutions

Given a solution `a` of (akeqn)–(akeqn2) on `[0, 𝔇]` in the class `Z^{d+1}` with rapidly
decreasing data `c`, and `α = L^{-γ}`, `σ = δ T_kin`, `M = L^{-d} ∑ |cₙ|²`, the coefficients
`backCoeff L γ δ c a s n = e^{i(2αM + 2π|k|²)s} aₙ(s/σ)` (inverse of (reducedcoef) and of the
Wick-ordering gauge; mass is conserved, so the gauge factor is explicit) satisfy the Fourier-side
NLS system `∂ₛ ûₙ = i(2π|k|² ûₙ + α cubicConv(û)ₙ)` on `[0, T]`, `T = σ 𝔇`
(`hasDerivWithinAt_backCoeff`).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- Gauge covariance of the Wick-ordered convolution. -/
theorem wickConv_const_mul (L : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (b : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) : wickConv L (fun m => z * b m) n = z * wickConv L b n := by
  unfold wickConv
  have hzz := norm_mul_conj_eq_one hz
  have h : ∀ p : (Fin d → ℤ) × (Fin d → ℤ),
      (epsCoef p.1 p.2 (n - p.1 + p.2) : ℂ) *
        (z * b p.1 * (starRingEnd ℂ) (z * b p.2) * (z * b (n - p.1 + p.2))) =
        z * ((epsCoef p.1 p.2 (n - p.1 + p.2) : ℂ) *
          (b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2))) := by
    intro p
    rw [map_mul]
    linear_combination ((epsCoef p.1 p.2 (n - p.1 + p.2) : ℂ) *
      (b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2)) * z) * hzz
  simp_rw [h, tsum_mul_left]
  ring

/-- The mass `M = L^{-d} ∑ |cₙ|²` of the data. -/
@[expose] def dataMass (L : ℝ) (c : (Fin d → ℤ) → ℂ) : ℝ := (L ^ d)⁻¹ * ∑' m, ‖c m‖ ^ 2

/-- The NLS coefficients `ûₙ(s) = e^{i(2αM + 2π|k|²)s} aₙ(s/σ)`, `α = L^{-γ}`, `σ = δ T_kin`,
built from a solution of the `a`-system (inverse of (reducedcoef), TARGET L540–L543). -/
@[expose] def backCoeff (L γ δ : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) (s : ℝ)
    (n : Fin d → ℤ) : ℂ :=
  exp ((((2 * L ^ (-γ) * dataMass L c + 2 * Real.pi * ‖latticePoint L n‖ ^ 2) * s : ℝ) : ℂ) * I) *
    a (s / (δ * kineticTime (L ^ (-γ)))) n

theorem norm_backCoeff (L γ δ : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) (s : ℝ)
    (n : Fin d → ℤ) :
    ‖backCoeff L γ δ c a s n‖ = ‖a (s / (δ * kineticTime (L ^ (-γ)))) n‖ := by
  rw [backCoeff, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

section Solutions

variable {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

/-- The Fourier-side NLS system for `backCoeff` on `[0, T]`, `T = δ T_kin 𝔇`. -/
theorem hasDerivWithinAt_backCoeff (hL : 0 < L) (hδ : 0 < δ) {T : ℝ}
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (ha : IsAkSolution L γ δ 𝔇 c a) {s : ℝ}
    (hs : s ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun r => backCoeff L γ δ c a r n)
      (I * (((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) * backCoeff L γ δ c a s n +
        ((L ^ (-γ) : ℝ) : ℂ) * cubicConv L (backCoeff L γ δ c a s) n)) (Icc 0 T) s := by
  have hkt : kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2 := kineticTime_rpow_neg hL γ
  set σ := δ * kineticTime (L ^ (-γ)) with hσ
  have hσ0 : 0 < σ := by rw [hσ, hkt]; positivity
  set t := s / σ with htdef
  have hmaps : MapsTo (fun r => r / σ) (Icc 0 T) (Icc 0 𝔇) := fun r hr =>
    ⟨div_nonneg hr.1 hσ0.le, by
      rw [div_le_iff₀ hσ0, mul_comm]; rw [hT] at hr; exact hr.2⟩
  have ht : t ∈ Icc 0 𝔇 := hmaps hs
  set M := dataMass L c with hM
  set α := L ^ (-γ) with hα
  set θ : ℝ := 2 * α * M + 2 * Real.pi * ‖latticePoint L n‖ ^ 2 with hθ
  -- derivative of `r ↦ a (r/σ) n`
  have hA : HasDerivWithinAt (fun r => a (r / σ) n)
      ((1 / σ) • aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n)
      (Icc 0 T) s := by
    have h1 := ha.2.2 t ht n
    have hh : HasDerivWithinAt (fun r : ℝ => r / σ) (1 / σ) (Icc 0 T) s :=
      (hasDerivWithinAt_id s _).div_const σ
    exact h1.scomp s hh hmaps
  -- derivative of the phase
  have hE : HasDerivWithinAt (fun r : ℝ => exp (((θ * r : ℝ) : ℂ) * I))
      (exp (((θ * s : ℝ) : ℂ) * I) * ((θ : ℂ) * I)) (Icc 0 T) s := by
    have h : HasDerivWithinAt (fun r : ℝ => (((θ * r : ℝ) : ℂ) * I)) ((θ : ℂ) * I) (Icc 0 T) s := by
      simpa using ((hasDerivWithinAt_id s (Icc 0 T)).const_mul θ).ofReal_comp.mul_const I
    exact h.cexp
  have hprod := hE.mul hA
  -- notation for the key identity
  set F := aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n with hFdef
  set κ : ℝ := δ / (2 * L ^ ((d : ℝ) - γ)) with hκ
  set V : (Fin d → ℤ) → ℂ := fun m =>
    exp (((Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L m‖ ^ 2 * t : ℝ) : ℂ) * I) * a t m with hVdef
  set G : ℂ := exp (((2 * α * M * s : ℝ) : ℂ) * I) with hG
  have hGn : ‖G‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hct : Real.pi * δ * L ^ (2 * γ) * t = 2 * Real.pi * s := by
    rw [htdef, hσ, hkt]
    field_simp
  -- `Eₘ Vₘ = aₘ(t)`
  have hEV : ∀ m, exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L m‖ ^ 2 * t)) : ℝ) * I) *
      V m = a t m := by
    intro m
    simp only [hVdef]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  have hPW := phase_mul_wickConv L (Real.pi * δ * L ^ (2 * γ)) t V n
  simp only [hEV] at hPW
  set Sq := ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
    (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
      exp (((Real.pi * δ * L ^ (2 * γ) * resonance L q.1 q.2 (n - q.1 + q.2) n * t : ℝ) : ℂ) * I) *
      a t q.1 * (starRingEnd ℂ) (a t q.2) * a t (n - q.1 + q.2) with hSqdef
  have hF : F = (κ : ℂ) * I * Sq := by
    rw [hFdef, aNonlin_eq_tsum_pairs]
    simp only [Int.cast_one, one_mul, mul_one]
    rfl
  -- `û(s) = G V`
  have hb : backCoeff L γ δ c a s = fun m => G * V m := by
    funext m
    simp only [backCoeff, hVdef, hG]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    have h := congrArg (fun x : ℝ => (x : ℂ) * ‖latticePoint L m‖ ^ 2) hct
    push_cast at h
    linear_combination (-1 : ℂ) * I * h
  have hW : wickConv L (backCoeff L γ δ c a s) n = G * wickConv L V n := by
    rw [hb, wickConv_const_mul L hGn]
  -- the phase of `ûₙ`
  set P : ℂ := exp (((Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) : ℂ) * I)
    with hP
  set E : ℂ := exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I)
    with hEdef
  have hPE : P * E = 1 := by
    rw [hP, hEdef, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  have hexp : exp (((θ * s : ℝ) : ℂ) * I) = G * P := by
    rw [hG, hP, ← Complex.exp_add]
    congr 1
    have h := congrArg (fun x : ℝ => (x : ℂ) * ‖latticePoint L n‖ ^ 2) hct
    push_cast at h ⊢
    rw [hθ]
    push_cast
    linear_combination (-1 : ℂ) * I * h
  -- constants
  have hLd : (L ^ d : ℝ) ≠ 0 := pow_ne_zero _ hL.ne'
  have hconst : (κ : ℂ) * ((L ^ d : ℝ) : ℂ) = (α : ℂ) * (σ : ℂ) := by
    rw [← ofReal_mul, ← ofReal_mul]
    congr 1
    have hP' : L ^ (-γ) * L ^ (2 * γ) = L ^ γ := by rw [← Real.rpow_add hL]; ring_nf
    have hLγ : L ^ γ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
    rw [hκ, hα, hσ, hkt, Real.rpow_sub hL, Real.rpow_natCast,
      show L ^ (-γ) * (δ * (L ^ (2 * γ) / 2)) = δ * (L ^ (-γ) * L ^ (2 * γ)) / 2 by ring, hP']
    field_simp
  have hσC : (σ : ℂ) ≠ 0 := ofReal_ne_zero.2 hσ0.ne'
  have hLdC : ((L ^ d : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hLd
  -- `Sq = L^d E W(V)`
  have hSq : Sq = ((L ^ d : ℝ) : ℂ) * (E * wickConv L V n) := by
    rw [hPW, ← mul_assoc, mul_inv_cancel₀ hLdC, one_mul]
  -- the key identity
  have hkey : exp (((θ * s : ℝ) : ℂ) * I) * ((1 / σ) • F) =
      I * (α : ℂ) * wickConv L (backCoeff L γ δ c a s) n := by
    have hσinv : (σ : ℂ)⁻¹ * σ = 1 := inv_mul_cancel₀ hσC
    rw [hexp, hW, hF, hSq, Complex.real_smul, ofReal_div, ofReal_one, one_div]
    linear_combination (G * (σ : ℂ)⁻¹ * I * wickConv L V n * κ * ((L ^ d : ℝ) : ℂ)) * hPE +
      (G * (σ : ℂ)⁻¹ * I * wickConv L V n) * hconst + (G * I * wickConv L V n * α) * hσinv
  -- the Wick identity and mass conservation
  have hsum : Summable fun m => ‖backCoeff L γ δ c a s m‖ := by
    simp_rw [norm_backCoeff]
    exact ha.summable_norm hL ht
  have hmass : (L ^ d)⁻¹ * ∑' m, ‖backCoeff L γ δ c a s m‖ ^ 2 = M := by
    simp_rw [norm_backCoeff]
    rw [ha.tsum_normSq_eq hL ht, hM, dataMass]
  have hwick := cubicConv_sub_two_mul_eq_wickConv L hsum n
  rw [hmass] at hwick
  convert hprod using 1
  · funext r
    rfl
  · rw [hkey, ← hwick]
    have hbn : backCoeff L γ δ c a s n = exp (((θ * s : ℝ) : ℂ) * I) * a (s / σ) n := rfl
    rw [hbn, hθ]
    push_cast
    ring

end Solutions

end WaveTurbulence.NLS
