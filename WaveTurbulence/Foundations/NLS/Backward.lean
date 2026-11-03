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

/-- The time derivative of `backCoeff` given by the Fourier-side NLS system. -/
@[expose] def backDeriv (L γ δ : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) (s : ℝ)
    (n : Fin d → ℤ) : ℂ :=
  (I * ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ)) * backCoeff L γ δ c a s n +
    (I * ((L ^ (-γ) : ℝ) : ℂ) * ((L ^ d : ℝ) : ℂ)⁻¹) *
      cubicCurve (backCoeff L γ δ c a) (fun t m => (starRingEnd ℂ) (backCoeff L γ δ c a t m))
        (backCoeff L γ δ c a) s n

theorem hasDerivWithinAt_backCoeff' (hL : 0 < L) (hδ : 0 < δ) {T : ℝ}
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (ha : IsAkSolution L γ δ 𝔇 c a) {s : ℝ}
    (hs : s ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun r => backCoeff L γ δ c a r n) (backDeriv L γ δ c a s n) (Icc 0 T) s := by
  refine (hasDerivWithinAt_backCoeff hL hδ hT ha hs n).congr_deriv ?_
  simp only [backDeriv, cubicConv, cubicCurve]
  ring

theorem norm_two_pi_latticePoint_sq_le {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    ‖I * ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (2 * Real.pi * (1 + d / L ^ 2)) * (1 + ‖n‖) ^ 2 := by
  rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := one_add_norm_latticePoint_sq_le hL n
  have : ‖latticePoint L n‖ ^ 2 ≤ (1 + d / L ^ 2) * (1 + ‖n‖) ^ 2 := by linarith
  calc 2 * Real.pi * ‖latticePoint L n‖ ^ 2 ≤ 2 * Real.pi * ((1 + d / L ^ 2) * (1 + ‖n‖) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The coefficient curve built from an `a`-system solution with rapidly decreasing data has
uniformly rapidly decaying time derivatives of every order. -/
theorem goodCurve_backCoeff (hL : 0 < L) (hδ : 0 < δ) {T : ℝ}
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (hc : IsRapidDecay c)
    (ha : IsAkSolution L γ δ 𝔇 c a) : ∀ m, GoodCurve T m (backCoeff L γ δ c a) := by
  have hkt : kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2 := kineticTime_rpow_neg hL γ
  have hσ0 : 0 < δ * kineticTime (L ^ (-γ)) := by rw [hkt]; positivity
  have hmaps : ∀ s ∈ Icc 0 T, s / (δ * kineticTime (L ^ (-γ))) ∈ Icc 0 𝔇 := fun r hr =>
    ⟨div_nonneg hr.1 hσ0.le, by
      rw [div_le_iff₀ hσ0, mul_comm]; rw [hT] at hr; exact hr.2⟩
  have hcont : ∀ n, ContinuousOn (fun s => backCoeff L γ δ c a s n) (Icc 0 T) := fun n s hs =>
    (hasDerivWithinAt_backCoeff' hL hδ hT ha hs n).continuousWithinAt
  have hrap : UnifRapid T (backCoeff L γ δ c a) := by
    intro N
    obtain ⟨C, hC⟩ := ha.exists_uniform_decay hL hc N
    exact ⟨C, fun s hs n => by rw [norm_backCoeff]; exact hC _ (hmaps s hs) n⟩
  have hstep : ∀ m, GoodCurve T m (backCoeff L γ δ c a) →
      GoodCurve T m (backDeriv L γ δ c a) := by
    intro m hb
    have h1 := hb.weight (fun n => I * ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ))
      (norm_two_pi_latticePoint_sq_le hL)
    have h2 := (hb.cubicCurve hb.conj hb).const_mul (I * ((L ^ (-γ) : ℝ) : ℂ) *
      ((L ^ d : ℝ) : ℂ)⁻¹)
    exact h1.add h2
  intro m
  induction m with
  | zero => exact ⟨hcont, hrap⟩
  | succ m ih =>
    exact ⟨hcont, hrap, backDeriv L γ δ c a, hstep m ih,
      fun n s hs => hasDerivWithinAt_backCoeff' hL hδ hT ha hs n⟩

/-- The NLS solution built from an `a`-system solution:
`u(s, x) = L^{-d/2} ∑ₙ ûₙ(s) e^{2πi (n/L)·x}` with `û = backCoeff`. -/
@[expose] def backSolution (L γ δ : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) (s : ℝ)
    (x : Fin d → ℝ) : ℂ :=
  torusSeries L (backCoeff L γ δ c a s) x

theorem UnifRapid.isRapidDecay {T : ℝ} {b : ℝ → (Fin d → ℤ) → ℂ} (hb : UnifRapid T b) {t : ℝ}
    (ht : t ∈ Icc 0 T) : IsRapidDecay (b t) := fun N => by
  obtain ⟨C, hC⟩ := hb N
  exact ⟨C, fun n => hC t ht n⟩

theorem goodCurve_backDeriv (hL : 0 < L) (hδ : 0 < δ) {T : ℝ}
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (hc : IsRapidDecay c)
    (ha : IsAkSolution L γ δ 𝔇 c a) (m : ℕ) : GoodCurve T m (backDeriv L γ δ c a) := by
  have hb := goodCurve_backCoeff hL hδ hT hc ha m
  have h1 := hb.weight (fun n => I * ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ))
    (norm_two_pi_latticePoint_sq_le hL)
  have h2 := (hb.cubicCurve hb.conj hb).const_mul (I * ((L ^ (-γ) : ℝ) : ℂ) *
    ((L ^ d : ℝ) : ℂ)⁻¹)
  exact h1.add h2

/-- **The first reduction, backward direction** (TARGET L540–L566; FINDINGS F8; Wave B proposal
B1.4 item 2): a solution of (akeqn)–(akeqn2) on `[0, 𝔇]` in the class `Z^{d+1}` with rapidly
decreasing data `c` gives a smooth solution of (NLS) on `[0, T]`, `T = δ T_kin 𝔇`, `α = L^{-γ}`,
with the same data and `|û(t, n)| = |aₙ(t / (δ T_kin))|`. -/
theorem IsAkSolution.isSmoothNLSSolution (hL : 0 < L) (hδ : 0 < δ) (h𝔇 : 0 < 𝔇) {T : ℝ}
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (hc : IsRapidDecay c)
    (ha : IsAkSolution L γ δ 𝔇 c a) :
    IsSmoothNLSSolution L (L ^ (-γ)) T c (backSolution L γ δ c a) ∧
      ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (backSolution L γ δ c a t) n‖ =
        ‖a (t / (δ * kineticTime (L ^ (-γ)))) n‖ := by
  have hkt : kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2 := kineticTime_rpow_neg hL γ
  have hT0 : 0 < T := by rw [hT, hkt]; positivity
  have hgood := goodCurve_backCoeff hL hδ hT hc ha
  have hb : UnifRapid T (backCoeff L γ δ c a) := (hgood 0).unifRapid
  have hb' : UnifRapid T (backDeriv L γ δ c a) :=
    (goodCurve_backDeriv hL hδ hT hc ha 0).unifRapid
  have hdb : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => backCoeff L γ δ c a s n)
      (backDeriv L γ δ c a t n) (Icc 0 T) t :=
    fun n t ht => hasDerivWithinAt_backCoeff' hL hδ hT ha ht n
  have hcoef : ∀ t ∈ Icc 0 T, ∀ n,
      torusFourierCoeff L (backSolution L γ δ c a t) n = backCoeff L γ δ c a t n :=
    fun t ht n => torusFourierCoeff_torusSeries hL (hb.isRapidDecay ht).summable_norm n
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hb0 : backCoeff L γ δ c a 0 = c := by
    funext n
    simp [backCoeff, congrFun ha.1 n]
  refine ⟨⟨?_, fun t ht x j => isTorusPeriodic_torusSeries hL.ne' _ j x,
    fun n => by rw [hcoef 0 h0 n, hb0], fun t ht x => ?_⟩,
    fun t ht n => by rw [hcoef t ht n, norm_backCoeff]⟩
  · -- smoothness on `[0, T] × ℝ^d`
    show ContDiffOn ℝ _ (fun p : ℝ × (Fin d → ℝ) =>
      ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ * stSeries L (backCoeff L γ δ c a) p) _
    exact contDiffOn_const.mul (contDiffOn_stSeries_infty hL hT0 hgood)
  · -- the equation
    set f := backSolution L γ δ c a t with hfdef
    set g := torusSeries L (backDeriv L γ δ c a t) with hgdef
    have hderiv : derivWithin (fun s => backSolution L γ δ c a s x) (Icc 0 T) t = g x := by
      have h := (hasDerivWithinAt_stSeries_time (L := L) hL hb hb' hdb ht x).const_mul
        (((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹)
      exact h.derivWithin (uniqueDiffOn_Icc hT0 t ht)
    have hfs : ContDiff ℝ ∞ f := contDiff_torusSeries hL (hb.isRapidDecay ht)
    have hf2 : ContDiff ℝ 2 f := hfs.of_le (by norm_cast)
    have hfp : IsTorusPeriodic L f := isTorusPeriodic_torusSeries hL.ne' _
    have hgc : Continuous g := continuous_torusSeries (hb'.isRapidDecay ht).summable_norm
    have hgp : IsTorusPeriodic L g := isTorusPeriodic_torusSeries hL.ne' _
    have hfc : Continuous f := hfs.continuous
    have hc1 : Continuous fun y => I * g y - normLaplacian f y :=
      (continuous_const.mul hgc).sub (continuous_normLaplacian hf2)
    have hc2 : Continuous fun y => ((L ^ (-γ) : ℝ) : ℂ) * (((‖f y‖ ^ 2 : ℝ) : ℂ) * f y) := by
      fun_prop
    have hE : (fun y => I * g y - normLaplacian f y +
        ((L ^ (-γ) : ℝ) : ℂ) * (((‖f y‖ ^ 2 : ℝ) : ℂ) * f y)) = fun _ => 0 := by
      refine eq_of_torusFourierCoeff_eq hL (hc1.add hc2) continuous_const ?_
        (IsTorusPeriodic.const 0) fun n => ?_
      · intro j y
        simp only [hfp j y, hgp j y, (hfp.normLaplacian) j y]
      · have hfcoef : torusFourierCoeff L f = backCoeff L γ δ c a t := funext (hcoef t ht)
        rw [torusFourierCoeff_add hc1.integrableOn_Icc hc2.integrableOn_Icc,
          torusFourierCoeff_sub (f := fun y => I * g y) (g := normLaplacian f)
            (continuous_const.mul hgc).integrableOn_Icc
            (continuous_normLaplacian hf2).integrableOn_Icc,
          torusFourierCoeff_const_mul, torusFourierCoeff_const_mul,
          torusFourierCoeff_torusSeries hL (hb'.isRapidDecay ht).summable_norm,
          torusFourierCoeff_normLaplacian' hL hf2 hfp, ← cubicConv_torusFourierCoeff hL hfs hfp,
          hfcoef]
        have hzero : torusFourierCoeff L (fun _ : Fin d → ℝ => (0 : ℂ)) n = 0 := by
          simp [torusFourierCoeff_eq_integral]
        rw [hzero]
        have hcc : cubicConv L (backCoeff L γ δ c a t) n = ((L ^ d : ℝ) : ℂ)⁻¹ *
            cubicCurve (backCoeff L γ δ c a)
              (fun t m => (starRingEnd ℂ) (backCoeff L γ δ c a t m)) (backCoeff L γ δ c a) t n :=
          rfl
        rw [hcc, backDeriv]
        linear_combination (((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) *
          backCoeff L γ δ c a t n +
          ((L ^ (-γ) : ℝ) : ℂ) * (((L ^ d : ℝ) : ℂ)⁻¹ * cubicCurve (backCoeff L γ δ c a)
            (fun t m => (starRingEnd ℂ) (backCoeff L γ δ c a t m)) (backCoeff L γ δ c a) t n)) *
          I_sq
    rw [hderiv]
    linear_combination congrFun hE x

end Solutions

end WaveTurbulence.NLS
