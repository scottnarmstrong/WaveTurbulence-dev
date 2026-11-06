/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.DecoratedLeafFactorization
/-! Exact finite weight redistribution through a convergent oscillatory decoration sum. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem weighted_decoration_sum {w d : ℕ} {K : Type*}
    (G : Garden w) (hp : G.IsPlain) (H : ActualInputLeaves G → Mom d → ℝ)
    (k : K → GNode G.tree → Mom d) (hk : ∀ κ, IsDecoration G (k κ))
    (root : Fin w → Mom d) (hr : ∀ κ j, k κ (GNode.root G.tree j) = root j)
    (a : K → ℂ) (m : ℕ)
    (hs : ∀ c : RootWeightChoices G d m, Summable fun κ =>
      a κ * ((rootChoiceSign G c : ℝ) : ℂ) *
        ∏ l : ActualInputLeaves G,
          (monomialLeafProfile H (rootCoordinateSlots G hp c) l (k κ l.1.toNode) : ℂ)) :
    ((∏ j, jbr (root j) ^ (2 * m) : ℝ) : ℂ) *
        ∑' κ, a κ * ∏ l : ActualInputLeaves G, (H l (k κ l.1.toNode) : ℂ) =
      ∑ c : RootWeightChoices G d m, ((rootChoiceSign G c : ℝ) : ℂ) *
        ∑' κ, a κ * ∏ l : ActualInputLeaves G,
          (monomialLeafProfile H (rootCoordinateSlots G hp c) l (k κ l.1.toNode) : ℂ) := by
  classical
  have he (κ : K) :
      ((∏ j, jbr (root j) ^ (2 * m) : ℝ) : ℂ) *
          (a κ * ∏ l : ActualInputLeaves G, (H l (k κ l.1.toNode) : ℂ)) =
        ∑ c : RootWeightChoices G d m, a κ * ((rootChoiceSign G c : ℝ) : ℂ) *
          ∏ l : ActualInputLeaves G,
            (monomialLeafProfile H (rootCoordinateSlots G hp c) l (k κ l.1.toNode) : ℂ) := by
    have hh := congrArg (fun x : ℝ => (x : ℂ))
      (decorated_weighted_leaf_product G hp H (k κ) (hk κ) m)
    simp only [hr κ, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sum] at hh
    calc
      _ = a κ * ((∏ l : ActualInputLeaves G, (H l (k κ l.1.toNode) : ℂ)) *
          ((∏ j, jbr (root j) ^ (2 * m) : ℝ) : ℂ)) := by ring
      _ = _ := by rw [Complex.ofReal_prod, hh, mul_sum]; simp only [mul_assoc]
  rw [← tsum_mul_left]
  rw [tsum_congr he]
  rw [Summable.tsum_finsetSum (fun c _ => hs c)]
  apply sum_congr rfl
  intro c _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  ring

end WaveTurbulence.LGSpine
