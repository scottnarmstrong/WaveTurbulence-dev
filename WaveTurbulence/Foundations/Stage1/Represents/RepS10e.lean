/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepS10d
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr7
public import WaveTurbulence.Foundations.Stage1.ClassCount.Final
public import WaveTurbulence.Foundations.Spine.NonregularFinal
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 10: the `WTPrefix` assembly of `Stage1ReductionAt`

`stage1ReductionGate_of_vineCase`: `Stage1ReductionGate` (`∃ C₀ ≥ 2, WTPrefix (Stage1ReductionAt C₀)`) from the two leafwise
gates (via `noVine_prefixN`) and the named input `WTPrefix VineCaseRepresents`.
CLASSCOUNT is the proved `ClassCount.classCount`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.LGSpine

/-- Enlarge `C₂` to dominate `K^(D+1)` (and `L₀` to `2`), using monotonicity of the property in the large constants. -/
theorem prefix_with_C2_ge {Q : WTParams → Prop} (hQ : WTPrefix Q) (hm : LargeConstantMonotone Q) (K : ℝ) :
    WTPrefix (fun P => Q P ∧ K ^ (P.D + 1) ≤ P.C₂ ∧ 2 ≤ P.L) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη' φin hφin τ hτ φ hsol
  obtain ⟨C1, hC1, ν₀, hν₀, hν⟩ := hη η hη' φin hφin τ hτ φ hsol
  refine ⟨C1, hC1, ν₀, hν₀, ?_⟩
  intro ν hν'
  obtain ⟨δ₀, hδ₀, hδ⟩ := hν ν hν'
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' D hD htime
  obtain ⟨C2, hC2, L₀, hL₀, hL⟩ := hδ δ hδ' D hD htime
  refine ⟨max C2 (max 1 (K ^ (D + 1))), hC2.trans (le_max_left _ _), max L₀ 2, hL₀.trans (le_max_left _ _), ?_⟩
  intro L hL'
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans hL'
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL'
  have hq := hL L hL0
  refine ⟨?_, le_trans (le_max_right 1 (K ^ (D + 1))) (le_max_right C2 _), hL2⟩
  · exact hm _ C1 (max C2 (max 1 (K ^ (D + 1)))) hC1 hC2 hδ'.1 hL2 le_rfl
      (le_max_left _ _) hq

theorem stage1ReductionGate_of_vineCase (hinc : LeafwiseIncoherentDecayGate)
    (hcoh : LeafwiseCoherentApproximationGate) (hvine : WTPrefix VineCaseRepresents) :
    Stage1ReductionGate := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := stage1ReductionAt_of_inputs ClassCount.classCount
  refine ⟨fun _ _ => C₀, fun _ _ => hC₀, ?_⟩
  have hQ := prefix_and (noVine_prefixN hinc hcoh) hvine noVineRepresentsAtN_mono vineCaseRepresents_mono
  have hm : LargeConstantMonotone (fun P => NoVineRepresentsAtN P ∧ VineCaseRepresents P) :=
    noVineRepresentsAtN_mono.and vineCaseRepresents_mono
  have hQ2 := prefix_with_C2_ge hQ hm (K : ℝ)
  exact prefix_map (fun P hP => hmain P hP.2.1 hP.2.2 hP.1.1 hP.1.2) hQ2

end WaveTurbulence.Represents
