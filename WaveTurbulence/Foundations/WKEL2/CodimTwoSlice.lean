/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisCoordinates
public import WaveTurbulence.Foundations.WKEL2.WeightedKernelLp

/-!
# Uniform decay integral on affine slices of codimension two

The transverse integral in research-note Proposition 6. Successive orthogonal
projections reduce it to the centered decay integral in dimension d - 2.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Two successive orthogonal slices with fixed Euclidean coordinate carriers. -/
@[expose] def codimTwoSlice {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) (t u : ℝ) (z : Mom (d - 1 - 1)) : Mom d :=
  axisSliceEquiv hθ (t, axisSliceEquiv hη (u, z))

/-- The codimension-two decay constant is independent of the affine slice. -/
theorem integral_codimTwoSlice_le (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) (k : Mom d) (t u : ℝ) :
    Integrable (fun z => japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z)) ∧
      (∫ z, japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z)) ≤
        ∫ z : Mom (d - 1 - 1), japaneseDecay (2 * s) z := by
  have hs0 : 0 ≤ s := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hs, hdR]
  have hdim : ((d - 1 - 1 : ℕ) : ℝ) < 2 * s := by
    rw [Nat.cast_sub (by omega : 1 ≤ d - 1), Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    linarith only [hs]
  let E := perpIsometry hθ
  let J := perpIsometry hη
  let c : Mom (d - 1) := E (perpPart θ k)
  let b : Mom (d - 1 - 1) := J (perpPart η c)
  have hi := (integrable_japaneseDecay (2 * s) hdim).comp_add_left b
  have hnorm (z : Mom (d - 1 - 1)) :
      ‖b + z‖ ≤ ‖k + codimTwoSlice hθ hη t u z‖ := by
    have hfirst := norm_perpPart_add_le hθ k t
      (E.symm (axisSliceEquiv hη (u, z)))
    have hsecond := norm_perpPart_add_le hη c u (J.symm z)
    have hfirst' : ‖c + axisSliceEquiv hη (u, z)‖ ≤
        ‖k + codimTwoSlice hθ hη t u z‖ := by
      have hn : ‖((perpPart θ k + E.symm (axisSliceEquiv hη (u, z)) : ↥(ℝ ∙ θ)ᗮ) : Mom d)‖ =
          ‖c + axisSliceEquiv hη (u, z)‖ := by
        change ‖perpPart θ k + E.symm (axisSliceEquiv hη (u, z))‖ = _
        rw [← E.norm_map (perpPart θ k + E.symm (axisSliceEquiv hη (u, z))),
          E.map_add, E.apply_symm_apply]
      rw [hn] at hfirst
      simpa only [codimTwoSlice, axisSliceEquiv_apply, add_assoc] using hfirst
    have hsecond' : ‖b + z‖ ≤ ‖c + axisSliceEquiv hη (u, z)‖ := by
      have hn : ‖((perpPart η c + J.symm z : ↥(ℝ ∙ η)ᗮ) : Mom (d - 1))‖ = ‖b + z‖ := by
        change ‖perpPart η c + J.symm z‖ = _
        rw [← J.norm_map (perpPart η c + J.symm z), J.map_add, J.apply_symm_apply]
      rw [hn] at hsecond
      simpa only [axisSliceEquiv_apply, add_assoc] using hsecond
    exact hsecond'.trans hfirst'
  have hp (z : Mom (d - 1 - 1)) :
      japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z) ≤
        japaneseDecay (2 * s) (b + z) := by
    unfold japaneseDecay
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact add_le_add (le_refl 1) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hnorm z))
    · linarith only [hs0]
  have hm : Measurable (fun z => japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z)) := by
    have hc : Continuous (fun z => 1 + ‖k + codimTwoSlice hθ hη t u z‖ ^ 2) := by
      simp only [codimTwoSlice, axisSliceEquiv_apply]
      fun_prop
    exact (hc.rpow_const (fun _ => Or.inl (by positivity))).measurable
  have hit : Integrable (fun z => japaneseDecay (2 * s) (k + codimTwoSlice hθ hη t u z)) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (japaneseDecay_nonneg _ _)]
      exact hp z)
  refine ⟨hit, (integral_mono hit hi hp).trans ?_⟩
  exact (integral_add_left_eq_self (japaneseDecay (2 * s)) b).le

end WaveTurbulence.WKEL2
