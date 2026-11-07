/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTDomain
public import WaveTurbulence.Foundations.Spine.Final3f
/-! # FLOWER-P5: extension of free frequencies by zero on the stubs -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder MeasureTheory
open scoped Classical

variable {w d : ℕ} {G : Garden w}

/-- Extension of a free frequency by zero on the designated branches. -/
noncomputable def ext0F {fix : GBranch G.tree → Option ℝ} (β : {b : GBranch G.tree // fix b = none} → ℝ) :
    GBranch G.tree → ℝ :=
  fun b => if h : fix b = none then β ⟨b, h⟩ else 0

theorem measurable_ext0F (fix : GBranch G.tree → Option ℝ) :
    Measurable (ext0F (G := G) (fix := fix)) := by
  refine measurable_pi_iff.mpr fun b => ?_
  unfold ext0F
  by_cases h : fix b = none
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

theorem ext0F_free {fix : GBranch G.tree → Option ℝ} (β : {b : GBranch G.tree // fix b = none} → ℝ)
    (b : GBranch G.tree) (h : fix b = none) : ext0F β b = β ⟨b, h⟩ := by
  unfold ext0F; simp [h]

theorem measurable_comp_ext0F (fix : GBranch G.tree → Option ℝ) (g : (GBranch G.tree → ℝ) → ℝ)
    (hg : Measurable g) :
    Measurable (fun β : {b : GBranch G.tree // fix b = none} → ℝ => g (ext0F β)) :=
  hg.comp (measurable_ext0F fix)

end WaveTurbulence.FlowerP5
