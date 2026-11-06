/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Sumint.Words
/-! Linearity of coordinate derivatives on their natural finite differentiability domain. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open NormBridgeScratch

theorem partialMom_sub {d : ℕ} (j : Fin d) (f g : Mom d → ℂ) (x : Mom d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialMom j (fun y => f y - g y) x = partialMom j f x - partialMom j g x := by
  unfold partialMom
  rw [fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

theorem wordD_sub {d : ℕ} (word : List (Fin d)) (f g : Mom d → ℂ)
    (hf : ContDiff ℝ word.length f) (hg : ContDiff ℝ word.length g) :
    wordD word (fun x => f x - g x) = fun x => wordD word f x - wordD word g x := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    have hf0 : ContDiff ℝ word.length f := hf.of_le (by simp)
    have hg0 : ContDiff ℝ word.length g := hg.of_le (by simp)
    change partialMom j (wordD word (fun x => f x - g x)) = _
    rw [ih hf0 hg0]
    have hf1 : ContDiff ℝ (1 + word.length : ℕ) f := by simpa only [List.length_cons, Nat.add_comm] using hf
    have hg1 : ContDiff ℝ (1 + word.length : ℕ) g := by simpa only [List.length_cons, Nat.add_comm] using hg
    funext x
    exact partialMom_sub j _ _ x
      ((ContDiff.differentiable (wordD_contDiff word 1 hf1) (by norm_num)) x)
      ((ContDiff.differentiable (wordD_contDiff word 1 hg1) (by norm_num)) x)

end WaveTurbulence.LGSpine
