/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.SchwartzKernel
public import WaveTurbulence.Foundations.Resonant.FrechetIntegral

/-!
# Fréchet differentiation of Schwartz resonant test functions

All local dominated-integral hypotheses are obtained from Schwartz seminorms.
The derivative in the external momentum is the resonant integral of the
three simultaneous momentum derivatives, as in TARGET (C.6).
-/

public section

open MeasureTheory Filter Topology Set
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- The resonant integral of a Schwartz test function of three momenta. -/
@[expose] noncomputable def schwartzResonant (f : 𝓢(MomTriple d, ℝ)) (k : Mom d) : ℝ :=
  resonantIntegral (fun k₁ k₂ k₃ => f (k₁, k₂, k₃)) k

/-- The three simultaneous momentum derivatives as a functional of the external direction. -/
@[expose] noncomputable def schwartzResonantDeriv (f : 𝓢(MomTriple d, ℝ))
    (k ℓ x : Mom d) : Mom d →L[ℝ] ℝ :=
  (fderiv ℝ f (triplePoint k ℓ x)).comp (diagonalCLM d)

/-- A scalar kernel's local decay follows directly from its Schwartz seminorms. -/
theorem exists_local_deltaKernel_schwartz
    (hd : 2 ≤ d) (f : 𝓢(MomTriple d, ℝ)) {M : ℝ} (hM : (d : ℝ) < M) (k₀ : Mom d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Mom d, ‖k - k₀‖ ≤ 1 →
      DeltaKernel (fun ℓ x => f (triplePoint k ℓ x))
        (fun ℓ => (C * (2 ^ M) ^ 2) * (1 + ‖k₀ + ℓ‖) ^ (-M)) (fun _ => k₀) M := by
  obtain ⟨C, hC, hb⟩ := exists_polynomial_decay_schwartz f (2 * M)
  refine ⟨C, hC, fun k hk => deltaKernel_triple_of_decay hd hM hC f.continuous ?_ hk⟩
  simpa only [Real.norm_eq_abs] using hb

/-- Continuity of the derivative kernel in its two free momenta. -/
theorem continuous_schwartzResonantDeriv (f : 𝓢(MomTriple d, ℝ)) (k : Mom d) :
    Continuous (Function.uncurry (schwartzResonantDeriv f k)) := by
  change Continuous (fun p : Mom d × Mom d =>
    (fderiv ℝ f (triplePoint k p.1 p.2)).comp (diagonalCLM d))
  let Df := SchwartzMap.fderivCLM ℝ (MomTriple d) ℝ f
  have hc : Continuous (fun z : MomTriple d => (Df z).comp (diagonalCLM d)) :=
    Df.continuous.clm_comp continuous_const
  have hp : Continuous (fun p : Mom d × Mom d => triplePoint k p.1 p.2) := by
    unfold triplePoint
    fun_prop
  simpa only [Df, SchwartzMap.fderivCLM_apply, Function.comp_def] using hc.comp hp

/-- Local decay of the derivative functional also follows from Schwartz seminorms. -/
theorem exists_local_deltaKernel_schwartz_deriv
    (hd : 2 ≤ d) (f : 𝓢(MomTriple d, ℝ)) {M : ℝ} (hM : (d : ℝ) < M) (k₀ : Mom d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Mom d, ‖k - k₀‖ ≤ 1 →
      DeltaKernel (fun ℓ x => ‖schwartzResonantDeriv f k ℓ x‖)
        (fun ℓ => (C * (2 ^ M) ^ 2) * (1 + ‖k₀ + ℓ‖) ^ (-M)) (fun _ => k₀) M := by
  let Df := SchwartzMap.fderivCLM ℝ (MomTriple d) ℝ f
  obtain ⟨C, hC, hb⟩ := exists_polynomial_decay_schwartz Df (2 * M)
  let g : MomTriple d → ℝ := fun z => ‖(fderiv ℝ f z).comp (diagonalCLM d)‖
  have hc : Continuous g := by
    have hh : Continuous (fun z : MomTriple d => ‖(Df z).comp (diagonalCLM d)‖) :=
      (Df.continuous.clm_comp continuous_const).norm
    simpa only [g, Df, SchwartzMap.fderivCLM_apply] using hh
  have hg : ∀ z, |g z| ≤ (C * ‖diagonalCLM d‖) * (1 + ‖z‖) ^ (-(2 * M)) := by
    intro z
    dsimp only [g]
    rw [abs_of_nonneg (norm_nonneg _)]
    have hcomp := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f z) (diagonalCLM d)
    have hb' : ‖fderiv ℝ f z‖ ≤ C * (1 + ‖z‖) ^ (-(2 * M)) := by
      simpa only [Df, SchwartzMap.fderivCLM_apply] using hb z
    exact (hcomp.trans (mul_le_mul_of_nonneg_right hb' (norm_nonneg _))).trans_eq (by ring)
  refine ⟨C * ‖diagonalCLM d‖, mul_nonneg hC (norm_nonneg _), fun k hk => ?_⟩
  exact deltaKernel_triple_of_decay hd hM (mul_nonneg hC (norm_nonneg _)) hc hg hk

/-- The affine three-momentum parametrization has derivative given by the diagonal map. -/
theorem hasFDerivAt_triplePoint (k ℓ x : Mom d) :
    HasFDerivAt (fun p => triplePoint p ℓ x) (diagonalCLM d) k := by
  have hi : HasFDerivAt (fun p : Mom d => p) (ContinuousLinearMap.id ℝ (Mom d)) k := hasFDerivAt_id k
  have h := (hi.add_const ℓ).prodMk
    (((hi.add_const ℓ).add_const x).prodMk (hi.add_const x))
  simpa only [triplePoint, diagonalCLM] using h

/-- Fréchet differentiation through the full resonant integral for a Schwartz kernel. -/
theorem hasFDerivAt_schwartzResonant_integral
    (hd : 2 ≤ d) (f : 𝓢(MomTriple d, ℝ)) (k : Mom d) :
    HasFDerivAt (schwartzResonant f) (deltaFDerivIntegral (schwartzResonantDeriv f k)) k := by
  let M : ℝ := (d : ℝ) + 1
  have hM : (d : ℝ) < M := by dsimp [M]; linarith
  obtain ⟨C, _hC, hF⟩ := exists_local_deltaKernel_schwartz hd f hM k
  obtain ⟨B, _hB, hG⟩ := exists_local_deltaKernel_schwartz_deriv hd f hM k
  change HasFDerivAt (fun p => deltaInt (fun ℓ x => f (triplePoint p ℓ x)))
    (deltaFDerivIntegral (schwartzResonantDeriv f k)) k
  apply hasFDerivAt_deltaInt_of_local_decay (U := Metric.ball k 1) Metric.isOpen_ball (by omega)
    (F := fun p ℓ x => f (triplePoint p ℓ x)) (G := schwartzResonantDeriv f)
  · intro p hp
    have hpk : ‖p - k‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hp
    exact hF p hpk.le
  · intro p hp
    have hpk : ‖p - k‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hp
    exact hG p hpk.le
  · intro p _
    exact continuous_schwartzResonantDeriv f p
  · intro p _ ℓ x
    simpa only [Function.comp_def, schwartzResonantDeriv] using
      (f.hasFDerivAt (triplePoint p ℓ x)).comp p (hasFDerivAt_triplePoint p ℓ x)
  · exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)

end WaveTurbulence.Resonant
