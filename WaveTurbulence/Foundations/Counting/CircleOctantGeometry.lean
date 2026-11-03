/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeDisc
import Mathlib.Tactic

/-!
# Disjoint central square and outer circular caps

The square of half-width `R/sqrt 2` and the four outer caps partition a
translated closed disc. Cutting on horizontal and vertical lines avoids
rounding the center or introducing lattice points on artificial diagonals.
Each cap consists of the outer-octant arc columns.
-/

public section

namespace WaveTurbulence.Counting

/-- At most one coordinate can lie strictly outside the inscribed square. -/
theorem circle_not_both_outside_square {R T x y : ℝ}
    (hT : 0 ≤ T) (hTR : 2*T^2 = R^2) (hxy : x^2+y^2 ≤ R^2) :
    ¬ (T < |x| ∧ T < |y|) := by
  rintro ⟨hx,hy⟩
  have hx2 := (sq_lt_sq₀ hT (abs_nonneg x)).mpr hx
  have hy2 := (sq_lt_sq₀ hT (abs_nonneg y)).mpr hy
  simp only [sq_abs] at hx2 hy2
  linarith only [hx2,hy2,hTR,hxy]

/-- The inscribed-square cut has the required exact quadratic scale. -/
theorem circle_octant_cut_sq (R : ℝ) : 2*(R/Real.sqrt 2)^2 = R^2 := by
  rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- Exact cardinality partition, uniformly in the real center. The square
contains its edges; both outer cap filters use a strict inequality. -/
theorem card_latticeDisc_eq_square_add_caps
    (c : EuclideanSpace ℝ (Fin 2)) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hTR : 2*T^2 = R^2) :
    (latticeDisc c R).card =
      ((latticeDisc c R).filter (fun n => |(n 0:ℝ)-c 0| ≤ T ∧ |(n 1:ℝ)-c 1| ≤ T)).card +
      ((latticeDisc c R).filter (fun n => T < |(n 0:ℝ)-c 0|)).card +
      ((latticeDisc c R).filter (fun n => T < |(n 1:ℝ)-c 1|)).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnorm : ‖WaveTurbulence.latticePoint 1 n-c‖^2 =
      ((n 0:ℝ)-c 0)^2+((n 1:ℝ)-c 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [WaveTurbulence.latticePoint,Fin.sum_univ_two]
  have hxy : ((n 0:ℝ)-c 0)^2+((n 1:ℝ)-c 1)^2 ≤ R^2 := by
    rw [← hnorm]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr ((mem_latticeDisc hR).mp hn)
  have hnot := circle_not_both_outside_square hT hTR hxy
  by_cases hx : |(n 0:ℝ)-c 0| ≤ T
  · by_cases hy : |(n 1:ℝ)-c 1| ≤ T
    · simp only [ite_eq_left (show |(n 0:ℝ)-c 0| ≤ T ∧ |(n 1:ℝ)-c 1| ≤ T from ⟨hx,hy⟩),ite_eq_right (not_lt.mpr hx),ite_eq_right (not_lt.mpr hy),add_zero]
    · simp only [ite_eq_right (show ¬ (|(n 0:ℝ)-c 0| ≤ T ∧ |(n 1:ℝ)-c 1| ≤ T) from
        fun h => hy h.2),ite_eq_right (not_lt.mpr hx),ite_eq_left (lt_of_not_ge hy),zero_add]
  · by_cases hy : |(n 1:ℝ)-c 1| ≤ T
    · simp only [ite_eq_right (show ¬ (|(n 0:ℝ)-c 0| ≤ T ∧ |(n 1:ℝ)-c 1| ≤ T) from
        fun h => hx h.1),ite_eq_left (lt_of_not_ge hx),ite_eq_right (not_lt.mpr hy),zero_add,add_zero]
    · exact (hnot ⟨lt_of_not_ge hx,lt_of_not_ge hy⟩).elim

/-- The central part is exactly the Cartesian product of the two closed
integer intervals, including all square-edge lattice points. -/
theorem card_latticeDisc_central_square
    (c : EuclideanSpace ℝ (Fin 2)) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hTR : 2*T^2 = R^2) :
    ((latticeDisc c R).filter (fun n =>
      |(n 0:ℝ)-c 0| ≤ T ∧ |(n 1:ℝ)-c 1| ≤ T)).card =
      (integerInterval (c 0-T) (c 0+T)).card *
        (integerInterval (c 1-T) (c 1+T)).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_bij (fun n _ => (n 0,n 1))
  · intro n hn
    obtain ⟨_,hx,hy⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_product.mpr
    rw [mem_integerInterval,mem_integerInterval]
    rcases abs_le.mp hx with ⟨hx1,hx2⟩
    rcases abs_le.mp hy with ⟨hy1,hy2⟩
    constructor <;> constructor <;> linarith only [hx1,hx2,hy1,hy2]
  · intro n hn m hm he
    ext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨hx1,hx2⟩ := (mem_integerInterval _ _ _).mp hx
    obtain ⟨hy1,hy2⟩ := (mem_integerInterval _ _ _).mp hy
    have hax : |(x:ℝ)-c 0| ≤ T := abs_le.mpr ⟨by linarith,by linarith⟩
    have hay : |(y:ℝ)-c 1| ≤ T := abs_le.mpr ⟨by linarith,by linarith⟩
    refine ⟨![x,y],Finset.mem_filter.mpr ⟨?_,?_,?_⟩,rfl⟩
    · apply (mem_latticeDisc hR).mpr
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      have he : ‖WaveTurbulence.latticePoint 1 ![x,y]-c‖^2 =
          ((x:ℝ)-c 0)^2+((y:ℝ)-c 1)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [WaveTurbulence.latticePoint,Fin.sum_univ_two]
      rw [he]
      have hxq := (sq_le_sq₀ (abs_nonneg _) hT).mpr hax
      have hyq := (sq_le_sq₀ (abs_nonneg _) hT).mpr hay
      simp only [sq_abs] at hxq hyq
      nlinarith only [hxq,hyq,hTR]
    · exact hax
    · exact hay

/-- The square-cardinality correction left after subtracting its two flat
height sums is bounded by one. This cancels the artificial edges uniformly
in both coordinates of the real center. -/
theorem abs_central_square_card_correction_le (c : EuclideanSpace ℝ (Fin 2))
    {T : ℝ} (hT : 0 ≤ T) :
    |((integerInterval (c 0-T) (c 0+T)).card:ℝ)*
        ((integerInterval (c 1-T) (c 1+T)).card:ℝ) -
      2*T*(((integerInterval (c 0-T) (c 0+T)).card:ℝ)+
        ((integerInterval (c 1-T) (c 1+T)).card:ℝ))+4*T^2| ≤ 1 := by
  have hx := card_integerInterval_eq_sawtooth (l := c 0-T) (u := c 0+T)
    (by linarith only [hT])
  have hy := card_integerInterval_eq_sawtooth (l := c 1-T) (u := c 1+T)
    (by linarith only [hT])
  rw [hx,hy]
  have he : (c 0+T-(c 0-T)-NumberTheory.sawtooth (c 0+T)-
      NumberTheory.sawtooth (-(c 0-T)))*
      (c 1+T-(c 1-T)-NumberTheory.sawtooth (c 1+T)-NumberTheory.sawtooth (-(c 1-T)))-
      2*T*((c 0+T-(c 0-T)-NumberTheory.sawtooth (c 0+T)-NumberTheory.sawtooth (-(c 0-T)))+
      (c 1+T-(c 1-T)-NumberTheory.sawtooth (c 1+T)-NumberTheory.sawtooth (-(c 1-T))))+4*T^2 =
      (NumberTheory.sawtooth (c 0+T)+NumberTheory.sawtooth (-(c 0-T)))*
        (NumberTheory.sawtooth (c 1+T)+NumberTheory.sawtooth (-(c 1-T))) := by ring
  rw [he,abs_mul]
  have hb (a b : ℝ) : |NumberTheory.sawtooth a+NumberTheory.sawtooth b| ≤ 1 := by
    exact (abs_add_le _ _).trans (by linarith only
      [NumberTheory.abs_sawtooth_le_half a,NumberTheory.abs_sawtooth_le_half b])
  exact (mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)

end WaveTurbulence.Counting
