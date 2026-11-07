/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.SpineInputs
public import WaveTurbulence.Foundations.FlowerTop.P7Late
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity

/-! Joint prefix for P7's full couple clause over LG gates and the two leafwise inputs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine Set Filter

theorem prefix_with_gamma_upper {Q : WTParams → Prop} (hQ : WTPrefix Q) :
    WTPrefix (fun P => Q P ∧ P.γ < 1) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact ⟨hQ L hL, hγ.2⟩

/-- The entire couple clause, with hE/GardenNum/CoupleNum and regular premises discharged. -/
theorem couple_clause_prefix (S : FlowerSpineInputsV3) (hcount : FinalCountGateHalf) :
    WTPrefix (fun P => 1 / 2 < P.γ → CoupleClauseAt P) := by
  obtain ⟨C₀, hC₀, hst⟩ := S.stage1Gate
  have hm1 : LargeConstantMonotone (fun P => Stage1ReductionAt (C₀ P.d P.γ) P) :=
    fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h =>
      stage1ReductionAt_largeConstantMonotone (C₀ P.d P.γ) P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  have hm2 := coarseSplicedAt_largeConstantMonotone
  have hm3 := ladderFourierAt_largeConstantMonotone
  have hm4 := finalCountHalf_largeConstantMonotone
  have hm5 := lowProfile_largeConstantMonotone
  have hQ45 := prefix_and hcount lowProfile_prefix hm4 hm5
  have hQ345 := prefix_and S.ladderGate hQ45 hm3 (hm4.and hm5)
  have hQ2345 := prefix_and S.coarseGate hQ345 hm2 (hm3.and (hm4.and hm5))
  have hQ0 := prefix_and hst hQ2345 hm1 (hm2.and (hm3.and (hm4.and hm5)))
  have hm0 := hm1.and (hm2.and (hm3.and (hm4.and hm5)))
  have hleaf := prefix_and
    (prefix_map (fun _ h => LeafwiseCoherentApproximationAt.toOrder0 h) S.leafCoherent)
    S.leafDecay leafwiseCoherentApproximation_largeConstantMonotone
    leafwiseIncoherentDecay_largeConstantMonotone
  have hmleaf := leafwiseCoherentApproximation_largeConstantMonotone.and
    leafwiseIncoherentDecay_largeConstantMonotone
  have hQ1 := prefix_with_wke_context (prefix_and hQ0 hleaf hm0 hmleaf)
  have hQ2 := prefix_with_stage1_small_fn hQ1
    ((hm0.and hmleaf).and wkeContext_largeConstantMonotone)
    (fun d γ => 6 * C₀ d γ) (fun d γ => by have := hC₀ d γ; omega)
  have hQ3 := prefix_with_gamma_upper (prefix_with_coherent_small_parameters hQ2)
  refine prefix_late hQ3 (fun P hP => ?_)
  by_cases hhalf : 1 / 2 < P.γ
  · have hlate := p7_clause_late C₀ hC₀ P (hP P.L le_rfl).2 (by
      intro L hL
      obtain ⟨⟨⟨abc, lf⟩, ctx⟩, ps, eta, hd, habs⟩ := (hP L hL).1.1
      obtain ⟨a,b,c,d,e⟩ := abc
      exact ⟨⟨⟨⟨a,b,c,d hhalf,e⟩,ctx⟩,ps,eta,hd,habs⟩,lf,(hP L hL).1.2⟩)
    exact hlate.mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall fun _ h => absurd h hhalf

end WaveTurbulence.FlowerTop
