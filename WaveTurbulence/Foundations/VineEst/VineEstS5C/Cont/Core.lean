/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Step3AtH

/-! # V5-CONT, core: continuity of the recentered local kernel in the three exterior clocks

`clRecentered_continuousOn`: at one state `(B, RD, hG, layer)` with the row eligibility of Step 3 (`CoupleEligible`,
`TreeEligible` for every row), for every output momentum `E` of the output set the recentered local kernel
`clRecenteredLocalKernel` (written at the boundary `sumintBoundary (G.sign a) E`) is continuous in `(t₀,t₁,t₂)` on the
closed cube `cubeSet qOut`.  The proof is the continuity half of `step3AtLeafH` (`hcontI` of `Step3AtH`): the kernel is the
clocked expression at the effective clocks `leafT` (a leaf lower child does not see its clock), the clocked expression is
continuous on the cube by dominated convergence over the lattice sum (`continuousOn_clockedExprEps`), the majorant being
the decay of the rows (`hres` from the gates, `rows_continuousH`).  No `BadClause`, no order hypothesis and no smallness of
`C₁` are used.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine
  WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
open scoped ENNReal

/-- The effective output times `leafT` are continuous in `t` (the case split is on propositions, not on `t`). -/
theorem continuous_leafT (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] :
    Continuous (leafT q b1 b2) := by
  unfold leafT
  by_cases h1 : b1 <;> by_cases h2 : b2 <;> simp only [h1, h2, ite_true, ite_false] <;> fun_prop

/-- `leafT` maps the cube to itself. -/
theorem mapsTo_leafT_cubeSet (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] :
    Set.MapsTo (leafT q b1 b2) (cubeSet q) (cubeSet q) := by
  intro t ht i
  unfold leafT
  by_cases h1 : b1 <;> by_cases h2 : b2 <;> simp only [h1, h2, ite_true, ite_false]
  · by_cases hi2 : i = 2
    · subst hi2; simp
    · by_cases hi1 : i = 1
      · subst hi1; simp
      · simpa [Function.update_of_ne hi1, Function.update_of_ne hi2] using ht i
  · by_cases hi2 : i = 1
    · subst hi2; simp
    · simpa [Function.update_of_ne hi2] using ht i
  · by_cases hi2 : i = 2
    · subst hi2; simp
    · simpa [Function.update_of_ne hi2] using ht i
  · exact ht i

end WaveTurbulence.VineEstS5C.Cont
