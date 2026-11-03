/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneSigned
public import WaveTurbulence.Foundations.WKEL2.WeightedMultiplier
public import WaveTurbulence.Foundations.WKE.Multilinear

/-!
# The weighted L² trilinear estimate for the first loss term

Research-note Proposition 6 and the j = 1 case of Theorem 7.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Borel measurability of the signed first loss operator. -/
theorem measurable_lossOne (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    {e : Mom d} (he : ‖e‖ = 1) {f g : Mom d → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hLf : MemLp (weightedFunction s f) 2) (hLg : MemLp (weightedFunction s g) 2) :
    Measurable (fun k => deltaInt (fun a b => f (k + a + b) * g (k + b))) := by
  let := resonantMeasure_finiteOnCompacts e (by omega : 2 ≤ d)
  obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_signed hd s hs
  have hm : Measurable (fun q : Mom d × (Mom d × Mom d) =>
      f (q.1 + q.2.1 + q.2.2) * g (q.1 + q.2.2)) :=
    (hf.comp (by fun_prop)).mul (hg.comp (by fun_prop))
  have hi : Measurable (fun k => ∫ p, f (k + p.1 + p.2) * g (k + p.2) ∂resonantMeasure e) :=
    hm.stronglyMeasurable.integral_prod_right.measurable
  have heq (k : Mom d) :
      deltaInt (fun a b => f (k + a + b) * g (k + b)) =
        (1 / 2 : ℝ) * ∫ p, f (k + p.1 + p.2) * g (k + p.2) ∂resonantMeasure e := by
    rw [integral_resonantMeasure_eq_two_deltaInt he (hb e he f g hf hg hLf hLg k).1]
    ring
  simp_rw [heq]
  exact measurable_const.mul hi

/-- Signed j = 1 trilinear estimate with the exact frozen norm and actual membership. -/
theorem exists_collisionTerm_one_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      MemLp (weightedFunction s (collisionTerm 1 f₁ f₂ f₃)) 2 ∧
      weightedL2Norm s (collisionTerm 1 f₁ f₂ f₃) ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : Mom d)
  let e := unitVec v
  have he : ‖e‖ = 1 := norm_unitVec hv
  obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_signed hd s hs
  refine ⟨C, hC, fun f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃ => ?_⟩
  let q : Mom d → ℝ := fun k => deltaInt (fun a b => f₂ (k + a + b) * f₃ (k + b))
  have hq : Measurable q := measurable_lossOne hd s hs he h₂ h₃ hL₂ hL₃
  have hqb (k : Mom d) : |q k| ≤ C * weightedL2Norm s f₂ * weightedL2Norm s f₃ :=
    (hb e he f₂ f₃ h₂ h₃ hL₂ hL₃ k).2
  have hprod := weightedL2_mul_bounded s hL₁ hq
    (C * weightedL2Norm s f₂ * weightedL2Norm s f₃)
      (mul_nonneg (mul_nonneg hC (weightedL2Norm_nonneg _ _)) (weightedL2Norm_nonneg _ _)) hqb
  have heq : collisionTerm 1 f₁ f₂ f₃ = fun k => f₁ k * q k := by
    funext k
    change deltaInt (fun a b => f₁ k * f₂ (k + a + b) * f₃ (k + b)) = _
    rw [show (fun a b => f₁ k * f₂ (k + a + b) * f₃ (k + b)) =
      (fun a b => f₁ k * (f₂ (k + a + b) * f₃ (k + b))) by funext a b; ring,
      WKE.deltaInt_smul]
  rw [heq]
  refine ⟨hprod.1, hprod.2.trans_eq ?_⟩
  ring

end WaveTurbulence.WKEL2
