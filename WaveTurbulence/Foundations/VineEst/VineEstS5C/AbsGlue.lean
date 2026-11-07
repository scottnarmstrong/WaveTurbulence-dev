/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GenMerge

/-! # Absolute convergence of the glued summands from uniform `L¹` bounds (V5 Step 4d part C, `hAbs`)

`UAbs R L base Ψ C`: for every exterior time and boundary, the summand `Ψ` of the region `R` is integrable in the internal times
for every decoration, the `L¹` norms are summable over the decorations, with total at most `C`.
`SAbs RS L base ΨS C`: the same for an S-side summand `ΨS` (decoration, clock) over the decorations of the upper block, with total at most `C`.
`glueAbs_of_bounds`: if the S-side satisfies `SAbs` with `CS`, the T-side `UAbs` with `CT` (uniform in the boundary and the exterior times), the
summands are measurable and the glued summand factors, then the glued summands converge absolutely with total `≤ CS * CT`
(`GlueAbsConv`).  `uabs_glue`: the glued summand then satisfies `UAbs` of the union region with `CS * CT`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

theorem measurable_clock {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (t1 t2 : ℝ)
    (v : GBranch G.tree) : Measurable fun z : ℝ × CLInternalTime R => clLocalClock R ![z.1, t1, t2] z.2 v := by
  classical
  unfold clLocalClock
  by_cases ha : v = a
  · simp only [ha, dite_true]
    exact measurable_fst
  · by_cases hv : v ∈ U
    · simp only [ha, hv, dite_true, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [ha, hv, dite_false]
      split_ifs <;> simp

theorem measurable_clock_fun {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (t1 t2 : ℝ) :
    Measurable fun z : ℝ × CLInternalTime R => clLocalClock R ![z.1, t1, t2] z.2 :=
  measurable_pi_iff.mpr (measurable_clock R t1 t2)

theorem measurable_clock_fixed {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (t : Fin 3 → ℝ)
    (v : GBranch G.tree) : Measurable fun σ : CLInternalTime R => clLocalClock R t σ v := by
  classical
  unfold clLocalClock
  by_cases ha : v = a
  · simp only [ha, dite_true]; exact measurable_const
  · by_cases hv : v ∈ U
    · simp only [ha, hv, dite_true, dite_false]
      exact measurable_pi_apply _
    · simp only [ha, hv, dite_false]
      split_ifs <;> exact measurable_const

theorem measurable_clock_fixed_fun {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (t : Fin 3 → ℝ) : Measurable fun σ : CLInternalTime R => clLocalClock R t σ :=
  measurable_pi_iff.mpr (measurable_clock_fixed R t)

/-- Uniform `L¹` bound of a summand over the decorations of a region. -/
def UAbs {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ) : Prop :=
  ∀ (t : Fin 3 → ℝ) (β : Fin 4 → Mom d),
    (∀ κ : CLLocalDecoration R L base β,
      Integrable fun τ : CLInternalTime R => Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)) ∧
    Summable (fun κ : CLLocalDecoration R L base β =>
      ∫ τ : CLInternalTime R, ‖Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)‖) ∧
    ∑' κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R, ‖Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ ≤ C

/-- Uniform `L¹` bound of an S-side summand over the decorations of the upper block. -/
def SAbs {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d)
    (ΨS : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ) : Prop :=
  ∀ (t : Fin 3 → ℝ) (e f : Mom d),
    (∀ x : ExtS RS L base e f, Integrable fun σ : CLInternalTime RS => ΨS x.1 (clLocalClock RS t σ)) ∧
    Summable (fun x : ExtS RS L base e f => ∫ σ : CLInternalTime RS, ‖ΨS x.1 (clLocalClock RS t σ)‖) ∧
    ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖ΨS x.1 (clLocalClock RS t σ)‖ ≤ C

end WaveTurbulence.VineEstS5C
