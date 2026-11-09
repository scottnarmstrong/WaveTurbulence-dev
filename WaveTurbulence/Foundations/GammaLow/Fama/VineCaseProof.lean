/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCase
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone
public import WaveTurbulence.Foundations.Spine.LayergardenAssembly
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10d
public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstGamma
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD16
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr7
import Mathlib.Tactic
/-! # Item G (packet L5a-G): the vine case and the no-vine case of stage 1 over `𝒱_γ`

Proofs of L5a's interface statements (`Fama/VineCase.lean`), under L5a's instances
`[Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact TVineIsoInvariant]`:
* `vineCaseRepresentsLow_mono`, `noVineRepresentsLow_mono` (main's `RepS10d.*_mono` over `𝒱_γ`);
* `vineCaseLow (hT) : WTPrefix VineCaseRepresentsLow` (main's `RepVD16.vineCase_prefix`, with L5b's
  `Famb.vineEstGammaHalfMK` for main's `V5` and `Famb.normalChartSupply_of_tvine hT` for main's `hM9`);
* `noVineLow : WTPrefix NoVineRepresentsLow` (main's `RepPr7.noVine_prefixN`). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Represents

variable [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact TVineIsoInvariant]

/-- Main's `RepS10d.noVineRepresentsAtN_mono` over `𝒱_γ`. -/
theorem noVineRepresentsLow_mono : LargeConstantMonotone NoVineRepresentsLow := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  haveI : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  have hN' : D.size ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have hs0 : 0 ≤ s := (leafFamily_size_nonneg F _).trans hs
  have h1 := h hγ R S D hS layer hLayer p hp hN' hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) (by linarith) _ n tt base roots s hs0 _ h1

/-- Main's `RepS10d.vineCaseRepresents_mono` over `𝒱_γ`. -/
theorem vineCaseRepresentsLow_mono : LargeConstantMonotone VineCaseRepresentsLow := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  haveI : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize π hv
  have hRmax' : R ≤ 10 * P.R (p + 1) := by simpa only [R_largeConstants] using hRmax
  have hN' : N ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have h1 := h hγ p hp R hR hRmax' N hN1 hN' A (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG))
    hcl tt htt base roots U s hs0 hb hsize π hv
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) (by linarith) _ N tt base roots s hs0.le _ h1

/-- **Item G, vine case** (L5a's statement): main's `RepVD16.vineCase_prefix` over `𝒱_γ`, from main's leafwise gates
(`Spine.leafwise_incoherent_decay`, `Spine.leafwise_coherent_approximation`), L5b's `Famb.vineEstGammaHalfMK` (main's
V5) and the chart supply `Famb.normalChartSupply_of_tvine hT` (main's `hM9`). -/
theorem vineCaseLow (hT : TVine.Chart.TVineChartStatement) : WTPrefix VineCaseRepresentsLow :=
  Represents.vineCase_prefixLow Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation hT
    Famb.vineEstGammaHalfMK

/-- **Item G, no-vine case** (L5a's statement): main's `RepPr7.noVine_prefixN` over `𝒱_γ`. -/
theorem noVineLow : WTPrefix NoVineRepresentsLow :=
  Represents.noVine_prefixLow Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation

/-- The vine case with L4's Theorem C (`TVine.Chart.tvineChart_holds`, proved unconditionally) discharged. -/
theorem vineCaseLow_uncond : WTPrefix VineCaseRepresentsLow :=
  vineCaseLow TVine.Chart.tvineChart_holds

end WaveTurbulence.GammaLow.Fama
