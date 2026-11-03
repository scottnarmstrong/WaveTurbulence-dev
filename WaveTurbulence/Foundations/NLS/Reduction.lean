/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkSystem
public import WaveTurbulence.Foundations.NLS.Energy

/-!
# The first reduction: from (NLS) to the `a`-system (TARGET L540–L566), forward direction

Let `u` be a smooth solution of (NLS) with `α = L^{-γ}` and `M = ⨍|u|²` its (conserved) mass.

* `wickGauge L α u` is `v = e^{-2iαMt} u` (L540); `IsSmoothNLSSolution.wickGauge_eq`: `v` solves the
  Wick-ordered equation `(i∂ₜ - Δ)v + α(|v|²v - 2⨍|v|²·v) = 0` (L541);
* `IsSmoothNLSSolution.hasDerivWithinAt_wickGauge`: on the Fourier side,
  `∂ₜ v̂(t,n) = i (2π|k|² v̂(t,n) + α wickConv L v̂(t) n)`;
* `reducedCoeff L γ δ u` is `a_k(t) = e^{-πiδL^{2γ}|k|²t} v̂(δ T_kin t, k)` of (reducedcoef), L543,
  `T_kin = kineticTime α`;
* `IsSmoothNLSSolution.hasDerivWithinAt_reducedCoeff`, `IsSmoothNLSSolution.reducedCoeff_zero`: if
  `T = δ T_kin 𝔇` then `a` satisfies (akeqn)–(akeqn2) on `[0, 𝔇]` with `a(0) = c` (L545–L554);
  the classed statement `IsSmoothNLSSolution.isAkSolution` is in `NLS/UniformDecay`;
* `norm_reducedCoeff`: `|a_k(t)| = |û(δ T_kin t, k)|`.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- The mass average `M = ⨍_{𝕋_L^d} |f|² = L^{-d} ∫_{[0,L]^d} |f|²` (TARGET L540). -/
@[expose] def massAvg (L : ℝ) (f : (Fin d → ℝ) → ℂ) : ℝ :=
  (L ^ d)⁻¹ * ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖f x‖ ^ 2

/-- The Wick-ordering gauge transform `v(t) = e^{-2iαMt} u(t)`, `M = ⨍|u(0)|²` (TARGET L540). -/
@[expose] def wickGauge (L α : ℝ) (u : ℝ → (Fin d → ℝ) → ℂ) (s : ℝ) (x : Fin d → ℝ) : ℂ :=
  exp (((-2 * α * massAvg L (u 0) * s : ℝ) : ℂ) * I) * u s x

/-- The reduced coefficients (reducedcoef), TARGET L543:
`a_k(t) = e^{-πi δ L^{2γ} |k|² t} v̂(δ T_kin t, k)`, with `α = L^{-γ}` and `T_kin = kineticTime α`. -/
@[expose] def reducedCoeff (L γ δ : ℝ) (u : ℝ → (Fin d → ℝ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) *
    torusFourierCoeff L (wickGauge L (L ^ (-γ)) u (δ * kineticTime (L ^ (-γ)) * t)) n

theorem norm_exp_ofReal_mul_I' (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem conj_exp_ofReal_mul_I (θ : ℝ) :
    (starRingEnd ℂ) (exp ((θ : ℂ) * I)) = exp (((-θ : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, map_mul, conj_ofReal, conj_I]
  push_cast
  ring_nf

theorem kineticTime_rpow_neg {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2 := by
  rw [kineticTime, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  have : L ^ (-γ * ((2 : ℕ) : ℝ)) = (L ^ (2 * γ))⁻¹ := by
    rw [← Real.rpow_neg hL.le]
    congr 1
    push_cast
    ring
  rw [this]
  have hpos : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  field_simp

theorem torusFourierCoeff_wickGauge (L α : ℝ) (u : ℝ → (Fin d → ℝ) → ℂ) (s : ℝ)
    (n : Fin d → ℤ) :
    torusFourierCoeff L (wickGauge L α u s) n =
      exp (((-2 * α * massAvg L (u 0) * s : ℝ) : ℂ) * I) * torusFourierCoeff L (u s) n :=
  torusFourierCoeff_const_mul _ (u s) n

section Solutions

variable {L α T : ℝ} {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ}

theorem IsSmoothNLSSolution.massAvg_eq (hL : 0 < L) (hu : IsSmoothNLSSolution L α T c u)
    (h0 : (0 : ℝ) ∈ Icc 0 T) : massAvg L (u 0) = (L ^ d)⁻¹ * ∑' m, ‖c m‖ ^ 2 := by
  have hs0 := hasSum_sq_torusFourierCoeff hL (hu.contDiff h0).continuous (hu.isTorusPeriodic h0)
  simp only [hu.2.2.1] at hs0
  rw [massAvg, hs0.tsum_eq]

theorem IsSmoothNLSSolution.massAvg_eq_of_mem (hL : 0 < L) (hu : IsSmoothNLSSolution L α T c u)
    {s : ℝ} (hs : s ∈ Icc 0 T) : massAvg L (u s) = massAvg L (u 0) := by
  rw [massAvg, massAvg, hu.integral_normSq_eq hL hs]

/-- The Fourier side of the Wick-ordered equation:
`∂ₜ v̂(t,n) = i (2π|k|² v̂(t,n) + α L^{-d} ∑ ε v̂ conj v̂ v̂)` (TARGET L541–L566). -/
theorem IsSmoothNLSSolution.hasDerivWithinAt_wickGauge (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) {s : ℝ} (hs : s ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun r => torusFourierCoeff L (wickGauge L α u r) n)
      (I * (((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) *
          torusFourierCoeff L (wickGauge L α u s) n +
        α * wickConv L (torusFourierCoeff L (wickGauge L α u s)) n)) (Icc 0 T) s := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hs.1.trans hs.2⟩
  set M := massAvg L (u 0) with hM
  set g : ℝ → ℂ := fun r => exp (((-2 * α * M * r : ℝ) : ℂ) * I) with hgdef
  have hg : HasDerivWithinAt g (g s * (((-2 * α * M : ℝ) : ℂ) * I)) (Icc 0 T) s := by
    have h : HasDerivWithinAt (fun r : ℝ => (((-2 * α * M * r : ℝ) : ℂ) * I))
        (((-2 * α * M : ℝ) : ℂ) * I) (Icc 0 T) s := by
      simpa using
        ((hasDerivWithinAt_id s (Icc 0 T)).const_mul (-2 * α * M)).ofReal_comp.mul_const I
    exact h.cexp
  have hprod := hg.mul (hu.hasDerivWithinAt_torusFourierCoeff_eq hL hs n)
  have hfun : (fun r => torusFourierCoeff L (wickGauge L α u r) n) =
      fun r => g r * torusFourierCoeff L (u r) n :=
    funext fun r => torusFourierCoeff_wickGauge L α u r n
  have hcoef : torusFourierCoeff L (wickGauge L α u s) =
      fun m => g s * torusFourierCoeff L (u s) m :=
    funext fun m => torusFourierCoeff_wickGauge L α u s m
  have hgn : ‖g s‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsum : Summable fun m => ‖g s * torusFourierCoeff L (u s) m‖ := by
    simp_rw [norm_mul, hgn, one_mul]
    exact summable_norm_torusFourierCoeff hL (hu.contDiff hs) (hu.isTorusPeriodic hs)
  have hmass : ∑' m, ‖g s * torusFourierCoeff L (u s) m‖ ^ 2 = ∑' m, ‖c m‖ ^ 2 := by
    simp_rw [norm_mul, hgn, one_mul]
    exact (hu.hasSum_normSq_torusFourierCoeff hL hs).tsum_eq
  rw [hfun, hcoef, ← cubicConv_sub_two_mul_eq_wickConv L hsum n, cubicConv_const_mul L hgn,
    hmass, ← hu.massAvg_eq hL h0, ← hM]
  convert hprod using 1
  push_cast
  ring

/-- `v = e^{-2iαMt}u` solves the Wick-ordered equation `(i∂ₜ - Δ)v + α(|v|²v - 2⨍|v|²·v) = 0`
on `[0, T]` (TARGET L540–L541). -/
theorem IsSmoothNLSSolution.wickGauge_eq (hL : 0 < L) (hT : 0 < T)
    (hu : IsSmoothNLSSolution L α T c u) {s : ℝ} (hs : s ∈ Icc 0 T) (x : Fin d → ℝ) :
    I * derivWithin (fun r => wickGauge L α u r x) (Icc 0 T) s -
        normLaplacian (wickGauge L α u s) x +
      (α : ℂ) * ((((‖wickGauge L α u s x‖ ^ 2 : ℝ) : ℂ) * wickGauge L α u s x) -
        2 * (massAvg L (wickGauge L α u s) : ℂ) * wickGauge L α u s x) = 0 := by
  set M := massAvg L (u 0) with hM
  set z : ℂ := exp (((-2 * α * M * s : ℝ) : ℂ) * I) with hz
  have hzn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hg : HasDerivWithinAt (fun r : ℝ => exp (((-2 * α * M * r : ℝ) : ℂ) * I))
      (z * (((-2 * α * M : ℝ) : ℂ) * I)) (Icc 0 T) s := by
    have h : HasDerivWithinAt (fun r : ℝ => (((-2 * α * M * r : ℝ) : ℂ) * I))
        (((-2 * α * M : ℝ) : ℂ) * I) (Icc 0 T) s := by
      simpa using
        ((hasDerivWithinAt_id s (Icc 0 T)).const_mul (-2 * α * M)).ofReal_comp.mul_const I
    exact h.cexp
  have hderiv : derivWithin (fun r => wickGauge L α u r x) (Icc 0 T) s =
      z * (((-2 * α * M : ℝ) : ℂ) * I) * u s x +
        z * derivWithin (fun r => u r x) (Icc 0 T) s := by
    simp only [wickGauge]
    rw [derivWithin_fun_mul hg.differentiableWithinAt (hu.differentiableWithinAt hs x),
      hg.derivWithin (uniqueDiffOn_Icc hT s hs)]
  have hlap : normLaplacian (wickGauge L α u s) x = z * normLaplacian (u s) x := by
    simp only [normLaplacian, partialDeriv, wickGauge, ← hM, ← hz, deriv_const_mul_field',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmass : massAvg L (wickGauge L α u s) = M := by
    rw [hM, ← hu.massAvg_eq_of_mem hL hs]
    simp only [massAvg, wickGauge, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm : ‖wickGauge L α u s x‖ = ‖u s x‖ := by
    simp only [wickGauge, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hderiv, hlap, hmass, hnorm, show wickGauge L α u s x = z * u s x from rfl,
    hu.derivWithin_eq hs x]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The rescaled phase `e^{-πiδL^{2γ}|k|²t}`. -/
theorem hasDerivWithinAt_reducedPhase (L γ δ : ℝ) (n : Fin d → ℤ) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt
      (fun t => exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I))
      (exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) *
        (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2)) : ℝ) * I)) s t := by
  have h : HasDerivWithinAt
      (fun t : ℝ => (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) : ℂ) * I)
      (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2)) : ℝ) * I) s t := by
    have := ((hasDerivWithinAt_id t s).const_mul
      (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2))).ofReal_comp.mul_const I
    convert this using 2
    · simp only [id]; push_cast; ring
    · simp
  exact h.cexp

/-- The phase identity behind (akeqn2): with `Eₘ = e^{-ic|kₘ|²t}`,
`Eₙ v₁ conj v₂ v₃ = e^{icΩt} (E₁v₁) conj(E₂v₂) (E₃v₃)`. -/
theorem phase_mul_cubic (L c t : ℝ) (n n₁ n₂ n₃ : Fin d → ℤ) (v₁ v₂ v₃ : ℂ) :
    exp (((-(c * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) * (v₁ * (starRingEnd ℂ) v₂ * v₃) =
      exp (((c * resonance L n₁ n₂ n₃ n * t : ℝ) : ℂ) * I) *
        (exp (((-(c * ‖latticePoint L n₁‖ ^ 2 * t)) : ℝ) * I) * v₁) *
        (starRingEnd ℂ) (exp (((-(c * ‖latticePoint L n₂‖ ^ 2 * t)) : ℝ) * I) * v₂) *
        (exp (((-(c * ‖latticePoint L n₃‖ ^ 2 * t)) : ℝ) * I) * v₃) := by
  rw [map_mul, conj_exp_ofReal_mul_I]
  have h : exp (((-(c * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) =
      exp (((c * resonance L n₁ n₂ n₃ n * t : ℝ) : ℂ) * I) *
        exp (((-(c * ‖latticePoint L n₁‖ ^ 2 * t)) : ℝ) * I) *
        exp (((-(-(c * ‖latticePoint L n₂‖ ^ 2 * t))) : ℝ) * I) *
        exp (((-(c * ‖latticePoint L n₃‖ ^ 2 * t)) : ℝ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [resonance]
    push_cast
    ring
  rw [h]
  ring

theorem phase_mul_wickConv (L c t : ℝ) (V : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    exp (((-(c * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) * wickConv L V n =
      ((L ^ d : ℝ) : ℂ)⁻¹ * ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
        (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
          exp (((c * resonance L q.1 q.2 (n - q.1 + q.2) n * t : ℝ) : ℂ) * I) *
          (exp (((-(c * ‖latticePoint L q.1‖ ^ 2 * t)) : ℝ) * I) * V q.1) *
          (starRingEnd ℂ) (exp (((-(c * ‖latticePoint L q.2‖ ^ 2 * t)) : ℝ) * I) * V q.2) *
          (exp (((-(c * ‖latticePoint L (n - q.1 + q.2)‖ ^ 2 * t)) : ℝ) * I) *
            V (n - q.1 + q.2)) := by
  rw [wickConv, mul_left_comm, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun q => ?_
  rw [mul_left_comm, phase_mul_cubic L c t n q.1 q.2 (n - q.1 + q.2)]
  ring

theorem norm_reducedCoeff (L γ δ : ℝ) (u : ℝ → (Fin d → ℝ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    ‖reducedCoeff L γ δ u t n‖ =
      ‖torusFourierCoeff L (u (δ * kineticTime (L ^ (-γ)) * t)) n‖ := by
  simp only [reducedCoeff, torusFourierCoeff_wickGauge, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul]

theorem IsSmoothNLSSolution.reducedCoeff_zero (hu : IsSmoothNLSSolution L α T c u) (γ δ : ℝ)
    (hα : α = L ^ (-γ)) : reducedCoeff L γ δ u 0 = c := by
  subst hα
  funext n
  simp [reducedCoeff, torusFourierCoeff_wickGauge, hu.2.2.1]

/-- **The first reduction**, equation part (TARGET L540–L566, forward direction): if `u` is a smooth
solution of (NLS) with `α = L^{-γ}` on `[0, T]`, `T = δ T_kin 𝔇`, then the reduced coefficients
`a_k(t) = e^{-πiδL^{2γ}|k|²t} v̂(δ T_kin t, k)` satisfy `∂ₜ aₖ = 𝒞₊(a, ā, a)ₖ(t)` within
`[0, 𝔇]` (L545–L554). See `IsSmoothNLSSolution.isAkSolution` for the full statement. -/
theorem IsSmoothNLSSolution.hasDerivWithinAt_reducedCoeff {γ δ 𝔇 : ℝ} (hL : 0 < L)
    (hδ : 0 ≤ δ) (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇)
    (hu : IsSmoothNLSSolution L (L ^ (-γ)) T c u) {t : ℝ} (ht : t ∈ Icc 0 𝔇) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => reducedCoeff L γ δ u s n)
      (aNonlin L γ δ 1 t (reducedCoeff L γ δ u t)
        (fun m => (starRingEnd ℂ) (reducedCoeff L γ δ u t m)) (reducedCoeff L γ δ u t) n)
      (Icc 0 𝔇) t := by
  have hkt : kineticTime (L ^ (-γ)) = L ^ (2 * γ) / 2 := kineticTime_rpow_neg hL γ
  have hσ0 : 0 ≤ δ * kineticTime (L ^ (-γ)) := by rw [hkt]; positivity
  have hmaps : MapsTo (fun r => δ * kineticTime (L ^ (-γ)) * r) (Icc 0 𝔇) (Icc 0 T) :=
    fun r hr => ⟨mul_nonneg hσ0 hr.1, by rw [hT]; exact mul_le_mul_of_nonneg_left hr.2 hσ0⟩
  have hV := hu.hasDerivWithinAt_wickGauge hL (hmaps ht) n
  have hcomp := hV.scomp t ((hasDerivWithinAt_id t (Icc 0 𝔇)).const_mul
    (δ * kineticTime (L ^ (-γ)))) hmaps
  have hE := hasDerivWithinAt_reducedPhase L γ δ n (Icc 0 𝔇) t
  have hprod := hE.mul hcomp
  have hW := phase_mul_wickConv L (Real.pi * δ * L ^ (2 * γ)) t
    (torusFourierCoeff L (wickGauge L (L ^ (-γ)) u (δ * kineticTime (L ^ (-γ)) * t))) n
  have hP : L ^ (-γ) * L ^ (2 * γ) = L ^ γ := by rw [← Real.rpow_add hL]; ring_nf
  have hLd : (L ^ d : ℝ) ≠ 0 := pow_ne_zero _ hL.ne'
  have hLγ : L ^ γ ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hconst : ((L ^ (-γ) : ℝ) : ℂ) * ((δ * kineticTime (L ^ (-γ)) : ℝ) : ℂ) =
      ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * ((L ^ d : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← ofReal_mul]
    congr 1
    rw [hkt, Real.rpow_sub hL, Real.rpow_natCast,
      show L ^ (-γ) * (δ * (L ^ (2 * γ) / 2)) = δ * (L ^ (-γ) * L ^ (2 * γ)) / 2 by ring, hP]
    field_simp
  convert hprod using 1
  · funext r
    rfl
  rw [aNonlin, ← (resonantEquiv n).tsum_eq]
  simp only [Function.comp_apply, mul_one]
  have hsum : ∑' q, (fun p : {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) //
        p.1 - p.2.1 + p.2.2 = n} =>
      (epsCoef p.1.1 p.1.2.1 p.1.2.2 : ℂ) *
        exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) * resonance L p.1.1 p.1.2.1 p.1.2.2 n *
          t : ℝ) : ℂ) * I) * reducedCoeff L γ δ u t p.1.1 *
          (starRingEnd ℂ) (reducedCoeff L γ δ u t p.1.2.1) * reducedCoeff L γ δ u t p.1.2.2)
        ((resonantEquiv n) q) =
      ((L ^ d : ℝ) : ℂ) * (exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) *
        I) * wickConv L
          (torusFourierCoeff L (wickGauge L (L ^ (-γ)) u (δ * kineticTime (L ^ (-γ)) * t))) n) := by
    rw [hW, ← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.2 hLd), one_mul]
    refine tsum_congr fun q => ?_
    simp only [resonantEquiv, Equiv.coe_fn_mk, reducedCoeff, Int.cast_one, one_mul]
  rw [hsum]
  have hc1 : ((δ * kineticTime (L ^ (-γ)) : ℝ) : ℂ) * ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) =
      ((Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_mul]
    congr 1
    rw [hkt]
    ring
  rw [Complex.real_smul]
  generalize exp (((-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t)) : ℝ) * I) = E
  generalize torusFourierCoeff L (wickGauge L (L ^ (-γ)) u (δ * kineticTime (L ^ (-γ)) * t)) n = V
  generalize wickConv L
    (torusFourierCoeff L (wickGauge L (L ^ (-γ)) u (δ * kineticTime (L ^ (-γ)) * t))) n = W
  simp only [ofReal_neg]
  generalize ((L ^ (-γ) : ℝ) : ℂ) = α' at hconst ⊢
  generalize ((δ * kineticTime (L ^ (-γ)) : ℝ) : ℂ) = σ' at hconst hc1 ⊢
  generalize ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) = A at hconst ⊢
  generalize ((L ^ d : ℝ) : ℂ) = P at hconst ⊢
  generalize ((2 * Real.pi * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) = k2 at hc1 ⊢
  generalize ((Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 : ℝ) : ℂ) = ck2 at hc1 ⊢
  push_cast
  linear_combination (-(E * I * W)) * hconst + (-(E * I * V)) * hc1

end Solutions

end WaveTurbulence
