/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Squares for the Morrey estimate

All squares are closed; the geometric statements therefore include their
boundary. Lebesgue measure agrees with coordinate product measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The closed coordinate square with lower corner `a` and side `r`. -/
@[expose] def closedSquare (a : Fin 2 → ℝ) (r : ℝ) : Set (Mom 2) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + r}

theorem measurableSet_closedSquare (a : Fin 2 → ℝ) (r : ℝ) :
    MeasurableSet (closedSquare a r) := by
  have heq : closedSquare a r = ⋂ i : Fin 2,
      {x : Mom 2 | a i ≤ x i} ∩ {x : Mom 2 | x i ≤ a i + r} := by
    ext x
    simp only [closedSquare, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun x : Mom 2 => x i) := by fun_prop
  exact (measurableSet_le measurable_const hi).inter
    (measurableSet_le hi measurable_const)

theorem convex_closedSquare (a : Fin 2 → ℝ) (r : ℝ) : Convex ℝ (closedSquare a r) := by
  intro x hx y hy u v hu hv huv i
  change a i ≤ u * x i + v * y i ∧ u * x i + v * y i ≤ a i + r
  constructor
  · calc
      a i = u * a i + v * a i := by rw [← add_mul, huv, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx i).1 hu)
        (mul_le_mul_of_nonneg_left (hy i).1 hv)
  · calc
      u * x i + v * y i ≤ u * (a i + r) + v * (a i + r) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i).2 hu)
          (mul_le_mul_of_nonneg_left (hy i).2 hv)
      _ = a i + r := by rw [← add_mul, huv, one_mul]

/-- A closed square is compact, including the empty and zero-side cases. -/
theorem isCompact_closedSquare (a : Fin 2 → ℝ) (r : ℝ) :
    IsCompact (closedSquare a r) := by
  have heq : closedSquare a r = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      (Set.pi Set.univ (fun i : Fin 2 => Icc (a i) (a i + r))) := by
    ext x
    simp only [closedSquare, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ,
      forall_const, mem_Icc]
    rfl
  rw [heq]
  exact (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The coordinate-product volume of a square. -/
theorem volume_closedSquare (a : Fin 2 → ℝ) (r : ℝ) :
    volume (closedSquare a r) = ENNReal.ofReal r ^ 2 := by
  have heq : closedSquare a r = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun i : Fin 2 => Icc (a i) (a i + r))) := by
    ext x
    simp only [closedSquare, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, forall_const,
      mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet]
  simp only [volume_pi, Measure.pi_pi, Real.volume_Icc, add_sub_cancel_left,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A square of side `r` has diameter at most `2r`. -/
theorem norm_sub_le_two_mul_of_mem_closedSquare {a : Fin 2 → ℝ} {r : ℝ}
    {x y : Mom 2} (hx : x ∈ closedSquare a r) (hy : y ∈ closedSquare a r) :
    ‖x - y‖ ≤ 2 * r := by
  have hr : 0 ≤ r := by linarith [(hx 0).1, (hx 0).2]
  have hb (i : Fin 2) : (x i - y i) ^ 2 ≤ r ^ 2 := by
    have h1 : -r ≤ x i - y i := by linarith [(hx i).1, (hy i).2]
    have h2 : x i - y i ≤ r := by linarith [(hx i).2, (hy i).1]
    have hm := mul_nonneg (sub_nonneg.mpr h2)
      (show 0 ≤ r + (x i - y i) by linarith only [h1])
    nlinarith only [hm]
  have heq : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  nlinarith only [heq, hb 0, hb 1, norm_nonneg (x - y), hr]

/-- Every point of the unit square belongs to a square of any smaller side
which is itself contained in the unit square. -/
theorem exists_small_closedSquare {x : Mom 2} (hx : x ∈ closedSquare 0 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ a : Fin 2 → ℝ, x ∈ closedSquare a r ∧ closedSquare a r ⊆ closedSquare 0 1 := by
  let a : Fin 2 → ℝ := fun i => min (x i) (1 - r)
  refine ⟨a, ?_, ?_⟩
  · intro i
    refine ⟨min_le_left _ _, ?_⟩
    change x i ≤ min (x i) (1 - r) + r
    rw [← min_add_add_right]
    exact le_min (by linarith) (by simpa using (hx i).2)
  · intro y hy i
    have ha0 : 0 ≤ a i := le_min ((hx i).1) (sub_nonneg.mpr hr1)
    have ha1 : a i ≤ 1 - r := min_le_right _ _
    simp only [Pi.zero_apply, zero_add]
    constructor <;> linarith [(hy i).1, (hy i).2]

end WaveTurbulence.Analysis
