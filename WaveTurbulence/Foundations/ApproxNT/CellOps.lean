/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Core
public import WaveTurbulence.Foundations.ApproxNT.Kernel
public import WaveTurbulence.Foundations.Resonant.NTOmegainvSource
public import WaveTurbulence.Foundations.NTSP.Lemma67Final

/-!
# The principal value and the delta functional on one cell (packet NT6)

* `pvOp F = lim_{ν→∞} ∫∫ χ_∞(ν⟨x,y⟩)/⟨x,y⟩ F(x,y) dx dy`, the Cauchy principal value of
  DH23 (intappr), with the source's cutoff `χ_∞ = 1 - χ₀` (as `Resonant.bilinearFourierTruncation`
  with cutoff `χ₀` and zero frequencies);
* `NTSP.deltaInner F = ∫ |x|⁻¹ ∫_{x^⊥} F(x,w) dw dx`, the hyperplane reading of `δ(⟨x,y⟩)`
  (campaign decision D6), as in packet NT5.

For one cell `P = θ(x-p)θ(y-q)e(ξ·x+η·y)`: by DH21 Lemma 6.3 (`Resonant.dh21_lemma_6_3_square`)
the truncations are bounded by `M`, converge, and the error at scale `μ` is
`≤ M μ⁻¹ (1+|ξ|+|η|)`; and `deltaInner P = ∫_ℝ cellInt(s) ds` (by DH23 Lemma 6.7(2),
`NTSP.ntintlem_two`, and Fourier inversion for a fixed bump).
-/

public section

noncomputable section

open MeasureTheory Finset WithLp Filter Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- The `ν`-truncated principal value `∫∫ χ_∞(ν⟨x,y⟩)/⟨x,y⟩ F(x,y) dx dy`. -/
@[expose] def pvTrunc (ν : ℝ) (F : Mom d → Mom d → ℂ) : ℂ :=
  Resonant.bilinearFourierTruncation Fourier.chi0 ν F 0 0

/-- The Cauchy principal value `p.v. ∫∫ F(x,y)/⟨x,y⟩ dx dy`. -/
@[expose] def pvOp (F : Mom d → Mom d → ℂ) : ℂ := limUnder atTop fun ν : ℝ => pvTrunc ν F

/-- The amplitude of one cell, as a function of two momenta. -/
@[expose] def cellFn (p q ξ η : Mom d) (x y : Mom d) : ℂ := pairAmp p q ξ η (x, y)

theorem isPVCutoff_chi0 : Resonant.IsPVCutoff Fourier.chi0 where
  cont := (Fourier.chi0_contDiff (n := 0)).continuous
  compact := Fourier.chi0_hasCompactSupport
  even u := Fourier.chi0_even u
  near := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hu
    exact Fourier.chi0_eq_one hu.le

/-- The cell amplitude as a Resonant localized amplitude. -/
@[expose] def cellLoc (p q : Mom d) : Mom d → Mom d → ℂ :=
  Resonant.localizedAmplitude (thetaMom d) (thetaMom d) (fun _ _ => 1) 1 p q

theorem cellLoc_eq (p q x y : Mom d) : cellLoc p q x y = cellAmp p q x y := by
  simp [cellLoc, Resonant.localizedAmplitude, Resonant.cutoffScale, cellAmp, thetaC]

theorem unitPhase_two_pi (ξ x : Mom d) :
    Resonant.unitPhase 1 (inner ℝ ((2 * Real.pi) • ξ) x) = (𝐞 (inner ℝ x ξ) : ℂ) := by
  rw [Resonant.unitPhase, Real.fourierChar_apply, inner_smul_left, real_inner_comm]
  congr 1
  push_cast
  simp

theorem pvTrunc_cellFn (ν : ℝ) (p q ξ η : Mom d) :
    pvTrunc ν (cellFn p q ξ η) = Resonant.bilinearFourierTruncation Fourier.chi0 ν (cellLoc p q)
      ((2 * Real.pi) • ξ) ((2 * Real.pi) • η) := by
  simp only [pvTrunc, Resonant.bilinearFourierTruncation, Resonant.bilinearInvFourierInner,
    inner_zero_left, Resonant.unitPhase, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  have h1 := unitPhase_two_pi ξ x
  have h2 := unitPhase_two_pi η y
  simp only [Resonant.unitPhase, one_mul] at h1 h2
  rw [h1, h2, cellFn, pairAmp, cellLoc_eq, Circle.smul_def, smul_eq_mul, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  ring

theorem support_thetaC_sub {p x : Mom d} (h : Real.sqrt d < ‖x - p‖) : thetaC (x - p) = 0 := by
  by_contra hne
  have h1 : thetaMom d (x - p) ≠ 0 := by intro h0; apply hne; simp [thetaC, h0]
  have h2 := thetaMom_support_subset (d := d) h1
  rw [Metric.mem_closedBall, dist_zero_right] at h2
  linarith

/-- DH21 Lemma 6.3 for one cell. -/
theorem exists_pvCell (hd : 3 ≤ d) : ∃ M : ℝ, 0 < M ∧ ∀ p q ξ η : Mom d,
    (∀ ν : ℝ, 1 < ν → ‖pvTrunc ν (cellFn p q ξ η)‖ ≤ M) ∧
    Tendsto (fun ν : ℝ => pvTrunc ν (cellFn p q ξ η)) atTop (𝓝 (pvOp (cellFn p q ξ η))) ∧
    ‖pvOp (cellFn p q ξ η)‖ ≤ M ∧
    ∀ μ : ℝ, 1 < μ → ‖pvOp (cellFn p q ξ η) - pvTrunc μ (cellFn p q ξ η)‖ ≤
      M * μ⁻¹ * (1 + ‖ξ‖ + ‖η‖) := by
  have hθ1 : ContDiff ℝ 1 (thetaMom d) := contDiff_thetaMom.of_le (by exact_mod_cast le_top)
  obtain ⟨M, hM, h⟩ := Resonant.dh21_lemma_6_3_square hd isPVCutoff_chi0
    (Fourier.chi0_contDiff (n := 1)) hθ1 hθ1 hasCompactSupport_thetaMom hasCompactSupport_thetaMom
  refine ⟨M, hM, fun p q ξ η => ?_⟩
  obtain ⟨hb, ⟨v, hv, hvM⟩, hlow⟩ := h 1 1 le_rfl p q (fun _ _ => 1) continuous_const
    (fun _ => differentiable_const _) (fun _ _ => by simp) (fun _ _ _ => by simp) ξ η
  simp only [NNReal.coe_one, mul_one, one_pow] at hb hvM hlow
  have hv' : Tendsto (fun ν : ℝ => pvTrunc ν (cellFn p q ξ η)) atTop (𝓝 v) := by
    simp only [pvTrunc_cellFn]; exact hv
  have hpv : pvOp (cellFn p q ξ η) = v := hv'.limUnder_eq
  refine ⟨fun ν hν => by rw [pvTrunc_cellFn]; exact hb ν hν, hpv ▸ hv', hpv ▸ hvM,
    fun μ hμ => ?_⟩
  obtain ⟨w, hw, hwM⟩ := hlow μ hμ
  have hcont : Continuous (Function.uncurry (cellLoc (d := d) p q)) := by
    have : Function.uncurry (cellLoc (d := d) p q) = fun z => cellAmp p q z.1 z.2 := by
      funext z; exact cellLoc_eq p q z.1 z.2
    rw [this]
    exact ((continuous_thetaC (d := d)).comp (continuous_fst.sub continuous_const)).mul
      ((continuous_thetaC (d := d)).comp (continuous_snd.sub continuous_const))
  have hsx : ∀ x y, Real.sqrt d < ‖x - p‖ → cellLoc p q x y = 0 := fun x y h => by
    rw [cellLoc_eq, cellAmp, support_thetaC_sub h, zero_mul]
  have hsy : ∀ x y, Real.sqrt d < ‖y - q‖ → cellLoc p q x y = 0 := fun x y h => by
    rw [cellLoc_eq, cellAmp, support_thetaC_sub h, mul_zero]
  have hw' := (hv.sub (Resonant.tendsto_jointHighCross isPVCutoff_chi0 μ hcont hsx hsy
    ((2 * Real.pi) • ξ) ((2 * Real.pi) • η))).congr
    (fun ν => (Resonant.lowBilinearFourierTruncation_eq isPVCutoff_chi0 ν μ hcont hsx hsy _ _).symm)
  have hweq : w = v - pvTrunc μ (cellFn p q ξ η) := by
    rw [pvTrunc_cellFn]; exact tendsto_nhds_unique hw hw'
  rw [hpv, ← hweq]
  exact hwM

end WaveTurbulence.ApproxNT
