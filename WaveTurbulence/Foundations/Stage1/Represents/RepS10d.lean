/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepS10c
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 10: large-constant monotonicity of the producer's inputs
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineA WaveTurbulence.Reg.Skeleton

theorem leafFamily_size_nonneg {P : WTParams} {w : ℕ} (F : LeafFamily P w) (LG : LayeredGarden w) :
    0 ≤ F.size LG :=
  Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun ℓ _ => NNReal.coe_nonneg _

theorem noVineRepresentsAtN_mono : LargeConstantMonotone NoVineRepresentsAtN := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  have hN' : D.size ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have hs0 : 0 ≤ s := (leafFamily_size_nonneg F _).trans hs
  have h1 := h R S D hS layer hLayer p hp hN' hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) _ n tt base roots s hs0 _ h1

theorem vineCaseRepresents_mono : LargeConstantMonotone VineCaseRepresents := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize π hv
  have hRmax' : R ≤ 10 * P.R (p + 1) := by simpa only [R_largeConstants] using hRmax
  have hN' : N ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have h1 := h p hp R hR hRmax' N hN1 hN' A (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) hcl
    tt htt base roots U s hs0 hb hsize π hv
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) _ N tt base roots s hs0.le _ h1

end WaveTurbulence.Represents
