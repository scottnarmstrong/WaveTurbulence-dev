/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SelectedCoordinates
public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightMonotone
public import WaveTurbulence.Foundations.WKEL2.SquareFreeEnergy
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Weighted L² jets control point evaluation on Schwartz space

The whole-space Sobolev bound is applied to the actual coordinate derivatives.
Every selected derivative is one of the already-defined weighted jet coordinates.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ENNReal ContDiff

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Any word within the jet order has its exact frozen norm bounded by the jet norm. -/
theorem weightedL2Norm_jetWord_le (s : ℝ) (m : ℕ) (w : List (JetLetter d))
    (hw : w.length ≤ m) (f : 𝓢(Mom d, ℝ)) :
    weightedL2Norm s (jetWordCLM w f) ≤ ‖weightedJetCLM s m f‖ := by
  let i : JetIndex d m := ⟨⟨w.length, by omega⟩, w.get⟩
  have H := norm_le_pi_norm (weightedJetCLM s m f) i
  rw [norm_weightedJetCLM_coordinate] at H
  simpa only [i, List.ofFn_get] using H

/-- Every square-free derivative energy is bounded by the actual weighted jet norm squared. -/
theorem mixedEnergy_toLp_le_jet (s : ℝ) (hs : 0 ≤ s) (b : Fin d → Bool) (f : 𝓢(Mom d, ℝ)) :
    (∫⁻ x : Fin d → ℝ, ENNReal.ofReal
      (‖Analysis.mixedPartial d b (fun y => f (WithLp.toLp 2 y)) x‖ ^ 2)) ≤
        ENNReal.ofReal (‖weightedJetCLM s d f‖ ^ 2) := by
  simp_rw [mixedPartial_toLp_schwartz]
  let g := jetWordCLM ((selectedCoordinates d b).map Sum.inr) f
  have hm : Measurable (fun k : Mom d => ENNReal.ofReal (‖g k‖ ^ 2)) := by fun_prop
  have H := (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp hm
  change (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖g (WithLp.toLp 2 x)‖ ^ 2)) ≤ _
  rw [H]
  apply (lintegral_norm_sq_le_weighted_schwartz s hs g).trans
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (weightedL2Norm_nonneg _ _)
  exact weightedL2Norm_jetWord_le s d _ (by
    simpa only [List.length_map] using length_selectedCoordinates_le d b) f

/-- A finite weighted L² jet controls every point, with constant depending only on dimension. -/
theorem norm_apply_le_weightedJet (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    ‖f k‖ ≤ (2 : ℝ) ^ d * ‖weightedJetCLM s d f‖ := by
  let Φ := fun x : Fin d → ℝ => f (WithLp.toLp 2 x)
  have hM : ∀ b : Fin d → Bool, Measurable (fun x =>
      ENNReal.ofReal (‖Analysis.mixedPartial d b Φ x‖ ^ 2)) := by
    intro b
    dsimp only [Φ]
    simp_rw [mixedPartial_toLp_schwartz]
    fun_prop
  have Hpoint := ofReal_norm_sq_le_wholeSobolevL2Sq d (f := Φ) (by fun_prop) (WithLp.ofLp k)
  have HE := wholeSobolevL2Sq_le_mixedEnergy d Φ hM
  have Hsq : ENNReal.ofReal (‖f k‖ ^ 2) ≤
      ENNReal.ofReal (((2 : ℝ) ^ d * ‖weightedJetCLM s d f‖) ^ 2) := by
    have Hpoint' : ENNReal.ofReal (‖f k‖ ^ 2) ≤ 2 ^ d * wholeSobolevL2Sq d Φ := by
      simpa only [Φ, WithLp.toLp_ofLp] using Hpoint
    apply Hpoint'.trans
    apply (mul_le_mul_right HE (2 ^ d)).trans
    rw [lintegral_finsetSum _ (fun b _ => hM b)]
    calc
      _ ≤ 2 ^ d * ∑ _b : Fin d → Bool, ENNReal.ofReal (‖weightedJetCLM s d f‖ ^ 2) := by
        apply mul_le_mul_right
        exact Finset.sum_le_sum fun b _ => mixedEnergy_toLp_le_jet s hs b f
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [ENNReal.ofReal_pow (mul_nonneg (by positivity) (norm_nonneg _)),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
        ring
  have Hreal := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 Hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).1 Hreal

end WaveTurbulence.WKEL2
