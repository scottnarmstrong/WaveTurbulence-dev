/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.MinkAux

/-! # P4: `XNorm00Restr` ignores a null set of times (V5 Step 4d part C, boundary of the clock box)

`XNorm00Restr_le_of_null`: if `B' ⊆ B` and `B \ B'` is Lebesgue-null, the restriction norm on `B` is at most the one on `B'`
(`XNorm00` only sees each time slice a.e.).  `null_clock_hyperplane`: the hyperplane `{tt | tt i = c}` is null.  Used to drop the
boundary of the exterior clock `tt 0` where the strict layer window fails.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence MeasureTheory Set
open scoped ENNReal

theorem XNorm00Restr_le_of_null {r : ℕ} {V : Type*} (θ : ℝ) {B B' : Set (Fin r → ℝ)} (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) (hnull : volume (B \ B') = 0) :
    XNorm00Restr θ B K F ≤ XNorm00Restr θ B' K F := by
  classical
  unfold XNorm00Restr
  refine le_iInf₂ fun G hG => ?_
  let G' : (Fin r → ℝ) → V → ℂ := fun t v => if t ∈ B' then G t v else if t ∈ B then F t v else G t v
  have hG' : ∀ t ∈ B, ∀ v ∈ K, G' t v = F t v := fun t ht v hv => by
    by_cases h : t ∈ B'
    · simp only [G', h, ite_true]; exact hG t h v hv
    · simp only [G', h, ht, ite_true, ite_false]
  refine (iInf₂_le G' hG').trans (le_of_eq ?_)
  refine WaveTurbulence.VineEstS3.Mink.XNorm00_congr_ae θ fun v => ?_
  have : ∀ᵐ t : Fin r → ℝ, t ∉ B \ B' := measure_eq_zero_iff_ae_notMem.mp hnull
  refine this.mono fun t ht => ?_
  by_cases h : t ∈ B'
  · simp only [G', h, ite_true]
  · have hB : t ∉ B := fun hB => ht ⟨hB, h⟩
    simp only [G', h, hB, ite_false]

theorem null_clock_hyperplane {r : ℕ} (i : Fin r) (c : ℝ) : volume {tt : Fin r → ℝ | tt i = c} = 0 := by
  have := Measure.pi_hyperplane (fun _ : Fin r => (volume : Measure ℝ)) i c
  simpa [volume_pi] using this

end WaveTurbulence.VineEstS5C.P4
