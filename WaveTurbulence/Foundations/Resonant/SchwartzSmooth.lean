/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.SchwartzDifferentiation

/-!
# Smooth dependence on the full external momentum

For a Schwartz test function of the three collision momenta, the resonant
integral is `C∞` in the vector momentum `k`. Each derivative is obtained by
differentiating the test function in all three momentum slots simultaneously.
The proof uses finite-dimensional derivative reconstruction and induction on
the differentiability order; it does not infer vector smoothness from separate
smoothness on lines.
-/

public section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- A coordinate derivative of the test function along the three simultaneous momenta. -/
@[expose] noncomputable def schwartzDirectionalTest (f : 𝓢(MomTriple d, ℝ)) (j : Fin d) :
    𝓢(MomTriple d, ℝ) :=
  LineDeriv.lineDerivOp (diagonalCLM d (EuclideanSpace.single j 1)) f

/-- Fréchet derivative written with scalar resonant integrals in a finite basis. -/
theorem hasFDerivAt_schwartzResonant
    (hd : 2 ≤ d) (f : 𝓢(MomTriple d, ℝ)) (k : Mom d) :
    HasFDerivAt (schwartzResonant f)
      (∑ j : Fin d, schwartzResonant (schwartzDirectionalTest f j) k •
        basisCoordCLM (EuclideanSpace.basisFun (Fin d) ℝ).toBasis j) k := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let M : ℝ := (d : ℝ) + 1
  have hM : (d : ℝ) < M := by dsimp [M]; linarith
  obtain ⟨C, _hC, hG⟩ := exists_local_deltaKernel_schwartz_deriv hd f hM k
  have hGk := hG k (by simp)
  have hc := continuous_schwartzResonantDeriv f k
  have he : deltaFDerivIntegral (schwartzResonantDeriv f k) =
      ∑ j : Fin d, schwartzResonant (schwartzDirectionalTest f j) k • basisCoordCLM b j := by
    rw [clm_eq_sum_basisCoord b (deltaFDerivIntegral (schwartzResonantDeriv f k))]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [deltaFDerivIntegral_apply hGk hc (by omega : 0 < d) (b j)]
    unfold schwartzResonant resonantIntegral
    apply deltaInt_congr
    intro ℓ x
    simp only [schwartzResonantDeriv, ContinuousLinearMap.comp_apply, schwartzDirectionalTest,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, resonantKernel, triplePoint,
      b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change HasFDerivAt (schwartzResonant f)
    (∑ j : Fin d, schwartzResonant (schwartzDirectionalTest f j) k • basisCoordCLM b j) k
  rw [← he]
  exact hasFDerivAt_schwartzResonant_integral hd f k

/-- Smoothness at every finite order, simultaneously for all Schwartz test functions. -/
theorem contDiff_schwartzResonant_nat
    (hd : 2 ≤ d) (n : ℕ) (f : 𝓢(MomTriple d, ℝ)) : ContDiff ℝ n (schwartzResonant f) := by
  classical
  suffices h : ∀ n : ℕ, ∀ f : 𝓢(MomTriple d, ℝ), ContDiff ℝ n (schwartzResonant f) from h n f
  intro n
  induction n with
  | zero =>
    intro f
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ (schwartzResonant f) from
      fun k => (hasFDerivAt_schwartzResonant hd f k).differentiableAt).continuous
  | succ n ih =>
    intro f
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun k => ∑ j : Fin d, schwartzResonant (schwartzDirectionalTest f j) k •
      basisCoordCLM (EuclideanSpace.basisFun (Fin d) ℝ).toBasis j, ?_,
      fun k => hasFDerivAt_schwartzResonant hd f k⟩
    exact ContDiff.sum fun j _ => (ih (schwartzDirectionalTest f j)).smul_const _

/-- TARGET (C.5)–(C.6): the resonant integral of a Schwartz three-momentum test
function depends smoothly on the full external momentum. -/
theorem contDiff_resonantIntegral_schwartz
    (hd : 2 ≤ d) (f : 𝓢(MomTriple d, ℝ)) :
    ContDiff ℝ ∞ (fun k : Mom d => resonantIntegral (fun k₁ k₂ k₃ => f (k₁, k₂, k₃)) k) := by
  change ContDiff ℝ ∞ (schwartzResonant f)
  exact contDiff_infty.mpr fun n => contDiff_schwartzResonant_nat hd n f

end WaveTurbulence.Resonant
