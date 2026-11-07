/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVineEstM
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10d
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG10
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 11: `VineEstCanonLayerHalfMK` is monotone in the large constants
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree WaveTurbulence.LGSpine
open scoped ENNReal

theorem vineEstHalfMK_N (P : WTParams) (c₁ c₂ : ℝ) (p : ℕ) :
    ({P with C₁ := c₁, C₂ := c₂} : WTParams).N p = P.N p := by
  simp [WTParams.N, WTParams.R, WTParams.Rdown]

theorem vineEstHalfMK_mono : LargeConstantMonotone VineEstCanonLayerHalfMK := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam hrow
  have hN := vineEstHalfMK_N P c₁ c₂ (p + 1)
  have key := @h p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay
    (by rw [← hN]; exact hord) (by have := vineEstHalfMK_N P c₁ c₂ 1; rw [← this]; exact hcl) centre wBar lam hrow
  refine le_trans key (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 ≤ P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) :=
    Real.rpow_nonneg (by linarith) _
  have hleaf := WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀
  have hs : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hc : 0 ≤ P.C₁ * Real.sqrt P.δ := mul_nonneg (by linarith) hs
  have hcc : P.C₁ * Real.sqrt P.δ ≤ c₁ * Real.sqrt P.δ := mul_le_mul_of_nonneg_right h₁ hs
  have hpow := pow_le_pow_left₀ hc hcc (clLocalOrder2 RD hG R)
  have h1 : 0 ≤ (1 + |lam|) ^ (6 * P.η ^ 6) := Real.rpow_nonneg (by positivity) _
  show (1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _) ≤
    (1 + |lam|) ^ (6 * P.η ^ 6) * ((c₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _)
  gcongr

end WaveTurbulence.Represents
