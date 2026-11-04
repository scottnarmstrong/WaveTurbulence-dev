/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LinkAbsoluteBounds

/-!
# Removing the Wick mask

TARGET (incohproof12): the two punctured coordinate axes cost at most `2(5L)^d`,
uniformly in the bilinear frequency and the four localization parameters.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

variable {d : ℕ}

private theorem summable_pureLink {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d) :
    Summable (fun p => cutoffAmplitude L A p * WeylSums.e (linkPhase L s A p)) := by
  apply Summable.of_norm
  simpa only [norm_mul, WeylSums.norm_e, mul_one] using summable_norm_cutoffAmplitude hL A

/-- The literal unmasked factor is exactly the landed lattice exponential sum. -/
theorem pureLink_eq_bilinearLatticeSum (L s : ℝ) (A : LinkParameters d) :
    (∑' p, cutoffAmplitude L A p * WeylSums.e (linkPhase L s A p)) =
      WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift := rfl

/-- F62: exact removal of the squared mask as the two axes with their common origin omitted. -/
theorem linkLatticeSum_eq_sub_axes {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d) :
    linkLatticeSum L s A =
      WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift -
        (∑' y, (if y = 0 then 0 else cutoffAmplitude L A (0, y) * WeylSums.e (linkPhase L s A (0, y)))) -
        (∑' x, (if x = 0 then 0 else cutoffAmplitude L A (x, 0) * WeylSums.e (linkPhase L s A (x, 0)))) := by
  classical
  let f := fun p => cutoffAmplitude L A p * WeylSums.e (linkPhase L s A p)
  have hf := summable_pureLink hL s A
  have hx : Summable (fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
      if p.1 = 0 then (if p.2 = 0 then 0 else f p) else 0) := by
    apply (hf.indicator {p | p.1 = 0 ∧ p.2 ≠ 0}).congr
    intro p
    by_cases hx0 : p.1 = 0 <;> by_cases hy0 : p.2 = 0 <;>
      simp [hx0, hy0, f]
  have hy : Summable (fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
      if p.2 = 0 then (if p.1 = 0 then 0 else f p) else 0) := by
    apply (hf.indicator {p | p.2 = 0 ∧ p.1 ≠ 0}).congr
    intro p
    by_cases hx0 : p.1 = 0 <;> by_cases hy0 : p.2 = 0 <;>
      simp [hx0, hy0, f]
  have heq : linkLatticeSum L s A = ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
      (f p - (if p.1 = 0 then (if p.2 = 0 then 0 else f p) else 0) -
        (if p.2 = 0 then (if p.1 = 0 then 0 else f p) else 0)) := by
    apply tsum_congr
    intro p
    change (linkWickFactor p.1 p.2 : ℂ) * cutoffAmplitude L A p *
      WeylSums.e (linkPhase L s A p) = _
    by_cases hx0 : p.1 = 0 <;> by_cases hy0 : p.2 = 0 <;>
      simp [linkWickFactor, linkEpsilon, hx0, hy0, f]
  rw [heq, (hf.sub hx).tsum_sub hy, hf.tsum_sub hx]
  rw [hx.tsum_prod, hy.tsum_prod]
  have haxis (x : Fin d → ℤ) :
      (∑' y, if x = 0 then (if y = 0 then 0 else f (x, y)) else 0) =
        if x = 0 then ∑' y, (if y = 0 then 0 else f (x, y)) else 0 := by
    by_cases hx0 : x = 0 <;> simp only [hx0, ite_true, ite_false, tsum_zero]
  simp_rw [haxis]
  simp only [tsum_ite_eq]
  rfl

private theorem norm_tsum_punctured_le {α : Type*} [Zero α] [DecidableEq α]
    (f : α → ℂ) (hf : Summable (fun a => ‖f a‖)) :
    ‖∑' a, (if a = 0 then 0 else f a)‖ ≤ ∑' a, ‖f a‖ := by
  have hbound (a : α) : ‖if a = 0 then 0 else f a‖ ≤ ‖f a‖ := by
    by_cases ha : a = 0 <;> simp only [ha, ite_true, ite_false, norm_zero, norm_nonneg, le_refl]
  have hs : Summable (fun a => ‖if a = 0 then 0 else f a‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hf
  exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hbound hs hf)

/-- The punctured vertical axis has at most one vector lattice mass. -/
theorem norm_leftAxis_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (A : LinkParameters d) :
    ‖∑' y, (if y = 0 then 0 else cutoffAmplitude L A (0, y) * WeylSums.e (linkPhase L s A (0, y)))‖ ≤
      (5 * L) ^ d := by
  have hf := (summable_norm_cutoffAmplitude (zero_lt_one.trans_le hL) A).comp_injective
    (show Function.Injective (fun y : Fin d → ℤ => ((0 : Fin d → ℤ), y)) from
      fun _ _ h => congrArg Prod.snd h)
  calc
    _ ≤ ∑' y, ‖cutoffAmplitude L A (0, y) * WeylSums.e (linkPhase L s A (0, y))‖ :=
      norm_tsum_punctured_le _ (by simpa only [norm_mul, WeylSums.norm_e, mul_one, Function.comp_def] using hf)
    _ = WeylSums.latticeCutoff (latticePoint L 0 - A.leftCenter) *
        ∑' y, WeylSums.latticeCutoff (latticePoint L y - A.rightCenter) := by
      simp only [norm_mul, WeylSums.norm_e, mul_one, norm_cutoffAmplitude, tsum_mul_left]
    _ ≤ ∑' y, WeylSums.latticeCutoff (latticePoint L y - A.rightCenter) :=
      mul_le_of_le_one_left (tsum_nonneg fun _ => latticeCutoff_nonneg _) (latticeCutoff_le_one _)
    _ ≤ _ := tsum_latticeCutoff_le hL _

/-- The punctured horizontal axis satisfies the identical dimensional bound. -/
theorem norm_rightAxis_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (A : LinkParameters d) :
    ‖∑' x, (if x = 0 then 0 else cutoffAmplitude L A (x, 0) * WeylSums.e (linkPhase L s A (x, 0)))‖ ≤
      (5 * L) ^ d := by
  have hf := (summable_norm_cutoffAmplitude (zero_lt_one.trans_le hL) A).comp_injective
    (show Function.Injective (fun x : Fin d → ℤ => (x, (0 : Fin d → ℤ))) from
      fun _ _ h => congrArg Prod.fst h)
  calc
    _ ≤ ∑' x, ‖cutoffAmplitude L A (x, 0) * WeylSums.e (linkPhase L s A (x, 0))‖ :=
      norm_tsum_punctured_le _ (by simpa only [norm_mul, WeylSums.norm_e, mul_one, Function.comp_def] using hf)
    _ = (∑' x, WeylSums.latticeCutoff (latticePoint L x - A.leftCenter)) *
        WeylSums.latticeCutoff (latticePoint L 0 - A.rightCenter) := by
      simp only [norm_mul, WeylSums.norm_e, mul_one, norm_cutoffAmplitude, tsum_mul_right]
    _ ≤ ∑' x, WeylSums.latticeCutoff (latticePoint L x - A.leftCenter) :=
      mul_le_of_le_one_right (tsum_nonneg fun _ => latticeCutoff_nonneg _) (latticeCutoff_le_one _)
    _ ≤ _ := tsum_latticeCutoff_le hL _

/-- TARGET (incohproof12), with a fully explicit error constant. -/
theorem norm_linkLatticeSum_sub_bilinear_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ)
    (A : LinkParameters d) :
    ‖linkLatticeSum L s A -
      WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ ≤
      2 * (5 * L) ^ d := by
  rw [linkLatticeSum_eq_sub_axes (zero_lt_one.trans_le hL)]
  have heq (a b c : ℂ) : a - b - c - a = -(b + c) := by ring
  rw [heq, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add (norm_leftAxis_le hL s A)
    (norm_rightAxis_le hL s A)).trans_eq (by ring))

end WaveTurbulence.Incoh
