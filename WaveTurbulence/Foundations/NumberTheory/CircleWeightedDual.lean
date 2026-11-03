/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.MonotoneWeightedSums
public import WaveTurbulence.Foundations.NumberTheory.VdCBCircleDualAScale
public import WaveTurbulence.Foundations.NumberTheory.CircleDualWeightScale
import Mathlib.Tactic

/-!
# Actual circle dual sums with their stationary curvature weight

Finite Abel summation applies the proved A estimate to the positive
decreasing stationary amplitude. The resulting endpoint-block powers are
those of `(11/30,16/30)`. No B-process identity is assumed here.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The actual integer-column dual, including arbitrary translation phase,
with its positive stationary curvature weight. -/
theorem norm_sum_weighted_circleLatticeDualPhase_le (a : ℤ) (N : ℕ) (p q : ℝ)
    {R h Y : ℝ} (hR : 0 < R) (hh : 0 < h) (hY : 1 ≤ Y) (hhY : h ≤ Y)
    (hRY : Y^2 ≤ R*h^2) (ha : Y ≤ (a:ℝ)+1) (hb : (a:ℝ)+N+2 ≤ 4*Y)
    (hNY : (N:ℝ) ≤ 2*Y) :
    ‖∑ n ∈ Finset.Ioc a (a+N),
      (Real.sqrt R*h*(h^2+(n:ℝ)^2)^(-((3:ℝ)/4))) •
        expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)‖ ≤
      17179869184*((Real.sqrt R*h/Y^((3:ℝ)/2))*
        ((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30))) := by
  let b : ℤ → ℝ := fun n => Real.sqrt R*h*(h^2+(n:ℝ)^2)^(-((3:ℝ)/4))
  let A : ℝ := (R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hS (k : ℕ) (hk : k ≤ N) :
      ‖∑ n ∈ Finset.Ioc a (a+k),
        expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)‖ ≤ 17179869184*A := by
    have hkR : (k:ℝ) ≤ N := by exact_mod_cast hk
    exact norm_sum_circleLatticeDualPhase_add_linear_le a k p q hR hh hY hhY hRY ha
      (by linarith only [hkR,hb]) (hkR.trans hNY)
  have hanti : AntitoneOn b (Set.Ici (a+1)) := by
    intro i hi j hj hij
    have hiR : (a:ℝ)+1 ≤ i := by exact_mod_cast hi
    have hijR : (i:ℝ) ≤ j := by exact_mod_cast hij
    have hi0 : (0:ℝ) ≤ i := le_trans hYp.le (ha.trans hiR)
    have hbase : h^2+(i:ℝ)^2 ≤ h^2+(j:ℝ)^2 := by nlinarith only [hijR,hi0]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)) (by positivity)
  have hbound := norm_sum_Ioc_smul_le_of_prefix_bound
    (fun n => expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)) b a N hS
    (fun n _hn => by dsimp only [b]; positivity) hanti
  have hweight : b (a+1) ≤ Real.sqrt R*h/Y^((3:ℝ)/2) := by
    have hbase : Y^2 ≤ h^2+((a:ℝ)+1)^2 := by nlinarith only [ha,hYp.le,sq_nonneg h]
    have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hYp) hbase
      (by norm_num : -((3:ℝ)/4) ≤ 0)
    have he : (Y^2)^(-((3:ℝ)/4)) = Y^(-((3:ℝ)/2)) := by
      rw [← Real.rpow_natCast Y 2,← Real.rpow_mul hYp.le]
      norm_num
    rw [he,Real.rpow_neg hYp.le] at hp
    dsimp only [b]
    push_cast
    simpa only [div_eq_mul_inv,mul_assoc] using
      mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Real.sqrt R*h)
  calc
    _ ≤ (17179869184*A)*b (a+1) := hbound
    _ ≤ (17179869184*A)*(Real.sqrt R*h/Y^((3:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hweight (by dsimp only [A]; positivity)
    _ = _ := by dsimp only [A]; ring

/-- The weighted actual dual on a block comparable to the source endpoint
scale has the local powers consumed by the circle transfer. -/
theorem norm_sum_weighted_circleLatticeDualPhase_le_endpoint (a : ℤ) (N : ℕ) (p q : ℝ)
    {R h Y U : ℝ} (hR : 0 < R) (hh : 0 < h) (hY : 1 ≤ Y) (hU : 0 < U)
    (hhY : h ≤ Y) (hRY : Y^2 ≤ R*h^2) (ha : Y ≤ (a:ℝ)+1)
    (hb : (a:ℝ)+N+2 ≤ 4*Y) (hNY : (N:ℝ) ≤ 2*Y)
    (hscale : (h*Real.sqrt (R/U))/4 ≤ Y) :
    ‖∑ n ∈ Finset.Ioc a (a+N),
      (Real.sqrt R*h*(h^2+(n:ℝ)^2)^(-((3:ℝ)/4))) •
        expPhase (VdCB.circleLatticeDualPhase R h n+p*(n:ℝ)+q)‖ ≤
      68719476736*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  have hfirst := norm_sum_weighted_circleLatticeDualPhase_le a N p q hR hh hY hhY hRY ha hb hNY
  have hsecond := circle_dual_weight_endpoint_bound hR hh (zero_lt_one.trans_le hY) hU hscale
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hsecond (by norm_num)).trans_eq (by ring))

end WaveTurbulence.NumberTheory
