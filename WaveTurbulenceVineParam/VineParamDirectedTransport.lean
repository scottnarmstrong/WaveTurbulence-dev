/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamEnergyCertificates
public import WaveTurbulenceVineParam.VineParamTranslation
import Mathlib.Tactic

/-! # Relabeling and uniform translation for directed molecule decorations -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [AddCommGroup E]

/-- The actual outgoing-minus-incoming momentum at a directed atom. -/
@[expose] def directedFlow (ends : β → V×V) (v : V) (k : β → E) : E :=
  ∑ j,(-energySign ends v j) • k j

omit [Fintype β] in
/-- Relabeling atoms preserves every incidence sign. -/
theorem energySign_relabel (ends : β → V×V) (σ : V ≃ V) (v : V) (j : β) :
    energySign (fun e => (σ (ends e).1,σ (ends e).2)) (σ v) j=energySign ends v j := by
  simp only [energySign,σ.injective.eq_iff]

/-- Source momenta are unchanged by a bijective atom relabeling. -/
theorem directedFlow_relabel (ends : β → V×V) (σ : V ≃ V) (v : V) (k : β → E) :
    directedFlow (fun e => (σ (ends e).1,σ (ends e).2)) (σ v) k=directedFlow ends v k := by
  simp only [directedFlow,energySign_relabel]

/-- Uniform translation changes a flow by the signed degree only. -/
theorem directedFlow_translate (ends : β → V×V) (v : V) (k : β → E) (t : E) :
    directedFlow ends v (fun j => k j+t)=directedFlow ends v k+
      (∑ j,-energySign ends v j) • t := by
  simp only [directedFlow,smul_add,sum_add_distrib,sum_smul]

section Inner
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [AddCommGroup E] [InnerProductSpace ℝ E] in
/-- Molecular resonance is unchanged by a bijective atom relabeling. -/
theorem directedEnergy_relabel (ends : β → V×V) (σ : V ≃ V) (v : V) (k : β → E) :
    directedEnergy (fun e => (σ (ends e).1,σ (ends e).2)) (σ v) k=directedEnergy ends v k := by
  simp only [directedEnergy,energySign_relabel]

end Inner
end WaveTurbulence.Vine.Param
