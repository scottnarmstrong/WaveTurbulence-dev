/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeLinearity
public import WaveTurbulence.Foundations.Spine.ZeroRemainderNorm
/-! Coordinate-word derivatives commute with finite sums of sufficiently smooth functions. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch Finset

theorem wordD_add {d : ℕ} (word : List (Fin d)) (f g : Mom d → ℂ)
    (hf : ContDiff ℝ word.length f) (hg : ContDiff ℝ word.length g) :
    wordD word (fun x => f x + g x) = fun x => wordD word f x + wordD word g x := by
  have hg' : ContDiff ℝ word.length (fun x => - g x) := hg.neg
  have h := wordD_sub word f (fun x => - g x) hf hg'
  have h2 : wordD word (fun x => - g x) = fun x => - wordD word g x := by
    have h3 := wordD_sub word (fun _ => 0) g contDiff_const hg
    have h4 := wordD_zero_function (d := d) word
    simp only [zero_sub] at h3
    rw [h4] at h3
    simpa only [zero_sub] using h3
  simp only [sub_neg_eq_add] at h
  rw [h, h2]
  funext x
  simp [sub_eq_add_neg]

theorem wordD_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι) (word : List (Fin d)) (f : ι → Mom d → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ word.length (f i)) :
    wordD word (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, wordD word (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty] using wordD_zero_function word
  | insert a s ha ih =>
    simp only [sum_insert ha]
    have h1 : ContDiff ℝ word.length (f a) := hf a (mem_insert_self a s)
    have h2 : ContDiff ℝ word.length (fun x => ∑ i ∈ s, f i x) :=
      ContDiff.sum fun i hi => hf i (mem_insert_of_mem hi)
    rw [wordD_add word _ _ h1 h2, ih (fun i hi => hf i (mem_insert_of_mem hi))]

end WaveTurbulence.LGSpine
