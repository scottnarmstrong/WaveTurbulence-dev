/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Defs
/-! # FL-FACE: the one-dimensional face identity (supplement (9.1))

For `ω ≠ 0`, `∫_{A<u<B} e^{iωu} du = (e^{iωB} − e^{iωA})/(iω)` when `A < B` (and `0` otherwise). With
`A = max` of the lower endpoints and `B = min` of the upper endpoints, the indicator `1_{A<B}` times `e^{iωB}` is the
sum over the upper endpoints of their cells (first minimizer, above every lower endpoint), and `1_{A<B} e^{iωA}` is the
sum over the lower endpoints of their cells (first maximizer, below every upper endpoint). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory Set

/-- (9.1) on an open interval, written as an integral over the line. -/
theorem integral_ite_Ioo_phase (A B ω : ℝ) (hω : ω ≠ 0) :
    (∫ u : ℝ, if A < u ∧ u < B then Complex.exp (((ω * u : ℝ) : ℂ) * Complex.I) else 0) =
      if A < B then
        (Complex.exp (((ω * B : ℝ) : ℂ) * Complex.I) - Complex.exp (((ω * A : ℝ) : ℂ) * Complex.I)) /
          (Complex.I * ω)
      else 0 := by
  have hind : (fun u : ℝ => if A < u ∧ u < B then Complex.exp (((ω * u : ℝ) : ℂ) * Complex.I) else 0) =
      (Ioo A B).indicator (fun u : ℝ => Complex.exp ((Complex.I * ω) * u)) := by
    funext u
    simp only [Set.indicator, Set.mem_Ioo]
    split_ifs
    · congr 1; push_cast; ring
    · rfl
  rw [hind, integral_indicator measurableSet_Ioo]
  split_ifs with hAB
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hAB.le,
      integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hω))]
    congr 2 <;> congr 1 <;> push_cast <;> ring
  · rw [Ioo_eq_empty hAB, Measure.restrict_empty, integral_zero_measure]

/-- (9.1) with the endpoints given as the maximum of a finite family of lower values and the minimum of a finite
family of upper values, partitioned exactly by first maximizers/minimizers. -/
theorem integral_slice_eq_sum {α : Type*} (lo hi : Finset α) (hlo : lo.Nonempty) (hhi : hi.Nonempty)
    (f : α → ℝ) (r : α → ℕ) (hrlo : Set.InjOn r lo) (hrhi : Set.InjOn r hi) (ω : ℝ) (hω : ω ≠ 0) :
    (∫ u : ℝ, if (∀ D ∈ lo, f D < u) ∧ (∀ U ∈ hi, u < f U) then
        Complex.exp (((ω * u : ℝ) : ℂ) * Complex.I) else 0) =
      (Complex.I * ω)⁻¹ *
        ((∑ U ∈ hi, if IsFirstMin hi f r U ∧ (∀ D ∈ lo, f D < f U) then
            Complex.exp (((ω * f U : ℝ) : ℂ) * Complex.I) else 0) -
          ∑ D ∈ lo, if IsFirstMax lo f r D ∧ (∀ U ∈ hi, f D < f U) then
            Complex.exp (((ω * f D : ℝ) : ℂ) * Complex.I) else 0) := by
  have hc : ∀ u : ℝ, ((∀ D ∈ lo, f D < u) ∧ (∀ U ∈ hi, u < f U)) ↔
      (lo.sup' hlo f < u ∧ u < hi.inf' hhi f) := fun u => by
    rw [sup'_lt_iff, lt_inf'_iff]
  have hcU : ∀ U, (∀ D ∈ lo, f D < f U) ↔ lo.sup' hlo f < f U := fun U => (sup'_lt_iff hlo).symm
  have hcD : ∀ D, (∀ U ∈ hi, f D < f U) ↔ f D < hi.inf' hhi f := fun D => (lt_inf'_iff hhi).symm
  simp only [hc, hcU, hcD]
  rw [integral_ite_Ioo_phase _ _ ω hω,
    sum_isFirstMin hi hhi f r hrhi (fun x => lo.sup' hlo f < x)
      (fun x => Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)),
    sum_isFirstMax lo hlo f r hrlo (fun x => x < hi.inf' hhi f)
      (fun x => Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I))]
  split_ifs
  · rw [div_eq_inv_mul]
  · simp

section Faces

variable {w : ℕ} {T : Fin w → TTree}

theorem isUpper_of_mem_upSet {v : GBranch T} {E : FaceEnd T} (hE : E ∈ upSet v) : E.isUpper = true := by
  rcases mem_insert.1 hE with rfl | hE
  · rfl
  · obtain ⟨q, _, rfl⟩ := mem_image.1 hE
    rfl

theorem isUpper_of_mem_lowSet {v : GBranch T} {E : FaceEnd T} (hE : E ∈ lowSet v) : E.isUpper = false := by
  rcases mem_insert.1 hE with rfl | hE
  · rfl
  · obtain ⟨q, _, rfl⟩ := mem_image.1 hE
    rfl

theorem disjoint_upSet_lowSet (v : GBranch T) : Disjoint (upSet v) (lowSet v) :=
  disjoint_left.2 fun E hu hl => by
    have h1 := isUpper_of_mem_upSet hu
    rw [isUpper_of_mem_lowSet hl] at h1
    exact Bool.false_ne_true h1

theorem upSet_nonempty (v : GBranch T) : (upSet v).Nonempty := insert_nonempty _ _

theorem lowSet_nonempty (v : GBranch T) : (lowSet v).Nonempty := insert_nonempty _ _

/-- The rank is injective on the upper endpoints. -/
theorem rank_injOn_upper : Set.InjOn (FaceEnd.rank (T := T)) {E | E.isUpper = true} := by
  intro E hE E' hE' h
  cases E <;> cases E' <;> simp only [Set.mem_ofPred_eq, FaceEnd.isUpper, Bool.false_eq_true] at hE hE' ⊢
  · simp only [FaceEnd.rank] at h
    exact absurd h (ne_of_gt (Fintype.equivFin (GBranch T) _).isLt)
  · simp only [FaceEnd.rank] at h
    exact absurd h (ne_of_lt (Fintype.equivFin (GBranch T) _).isLt)
  · simp only [FaceEnd.rank] at h
    exact congrArg FaceEnd.parent ((Fintype.equivFin (GBranch T)).injective (Fin.ext h))

/-- The rank is injective on the lower endpoints. -/
theorem rank_injOn_lower : Set.InjOn (FaceEnd.rank (T := T)) {E | E.isUpper = false} := by
  intro E hE E' hE' h
  cases E <;> cases E' <;> simp only [Set.mem_ofPred_eq, FaceEnd.isUpper, Bool.true_eq_false] at hE hE' ⊢
  · simp only [FaceEnd.rank] at h
    omega
  · simp only [FaceEnd.rank] at h
    omega
  · simp only [FaceEnd.rank, add_left_inj] at h
    exact congrArg FaceEnd.child ((Fintype.equivFin (GBranch T)).injective (Fin.ext h))

theorem rank_injOn_upSet (v : GBranch T) : Set.InjOn FaceEnd.rank (upSet v : Set (FaceEnd T)) :=
  rank_injOn_upper.mono fun _ hE => isUpper_of_mem_upSet hE

theorem rank_injOn_lowSet (v : GBranch T) : Set.InjOn FaceEnd.rank (lowSet v : Set (FaceEnd T)) :=
  rank_injOn_lower.mono fun _ hE => isUpper_of_mem_lowSet hE

end Faces

section Layered

variable {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)

/-- The constraints of `kDomainFix` on the time `u` of a free node `v`, the other times being `t`. -/
abbrev sliceCond (v : GBranch LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) (u : ℝ) : Prop :=
  (∀ D ∈ lowSet v, endVal LG up v t D < u) ∧ (∀ U ∈ upSet v, u < endVal LG up v t U)

/-- **(9.1) at one selected node.** Integrating the phase `e^{iωu}` over the slice of the time `u` of `v` gives
`(iω)⁻¹` times the signed sum over the endpoints of `v` of their cells, each with the phase at the endpoint. -/
theorem integral_slice_faces (v : GBranch LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) (ω : ℝ)
    (hω : ω ≠ 0) :
    (∫ u : ℝ, if sliceCond LG up v t u then Complex.exp (((ω * u : ℝ) : ℂ) * Complex.I) else 0) =
      (Complex.I * ω)⁻¹ * ∑ E ∈ endChoices v, (if E.isUpper then (1 : ℂ) else -1) *
        if faceCell LG up v E t then Complex.exp (((ω * endVal LG up v t E : ℝ) : ℂ) * Complex.I) else 0 := by
  unfold sliceCond
  rw [integral_slice_eq_sum (lowSet v) (upSet v) (lowSet_nonempty v) (upSet_nonempty v) (endVal LG up v t)
    FaceEnd.rank (rank_injOn_lowSet v) (rank_injOn_upSet v) ω hω, endChoices,
    sum_union (disjoint_upSet_lowSet v), sub_eq_add_neg, ← sum_neg_distrib]
  congr 2
  · refine sum_congr rfl fun E hE => ?_
    simp only [faceCell, isUpper_of_mem_upSet hE, ite_true, one_mul]
  · refine sum_congr rfl fun E hE => ?_
    simp only [faceCell, isUpper_of_mem_lowSet hE, Bool.false_eq_true, ite_false, neg_one_mul]

end Layered

end WaveTurbulence.Flower.FlFace
