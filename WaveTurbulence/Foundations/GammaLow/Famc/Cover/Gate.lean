/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverFineBound
/-! # The counting cover over `𝒱_γ`: TARGET finalsbest2 for `𝒱_γ` choice data (packet L5c)

`fineSplicedChoicesGamma`: from ladderl1old (`LadderFourierAt`) and L6's finalcount1 over `𝒱_γ`
(`FinalCountGammaAt`), the fine spliced estimate (finalsbest2, TARGET L2078) holds for the spliced kernel of every
`𝒱_γ` subpro choice datum satisfying the decorated conclusions of subpro (`SubproConclusionsGamma`). The counting
choices are produced in L6's `Src.CountingChoices P.γ G P.d` (with `Src.CountingGeometry`, `Src.splicedCountingAdmissible`)
by the ported cover (`Cover/CoverTags.lean` … `Cover/CoverFineBound.lean`).

The only named input is `SubObjectsInput` (L3's `SubObjectsStatement`, N2 Theorem 1.15 (F1)), used for the facts
`FamFacts` (connectivity of a member minus one atom / minus its joints). No restriction on `γ` is needed: for
`γ > 1/2` the family is the drawn one and main's lemmas apply. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.Induct WaveTurbulence.LGSpine

/-- **TARGET finalsbest2 over `𝒱_γ`** (L2078, via the counting cover L2097–L2116, from finalcount1 over `𝒱_γ`). -/
theorem fineSplicedChoicesGamma (hSO : SubObjectsInput) (P : WTParams) (hfourier : LadderFourierAt P)
    (hcount : FinalCount.FinalCountGammaAt P) (hs : CoverSmall P) : FineSplicedChoicesGammaAt P := by
  intro p R hp hR hRmax G hplain hirred hbal hn hnmax D hD hlayer hM hconn hatoms hbonds Cs base roots hS
  exact fine_spliced_of_subpro_choices P (famFacts_of_subObjects hSO P.γ) hfourier hcount hs.L_ge hs.delta_pos
    hs.c1_ge hs.delta_le hs.cap hs.cap_le hs.delta_exp hs.scale_log hs.count_const hp hR hRmax G hplain hirred hbal
    hn hnmax D hD hlayer hM hconn hatoms hbonds Cs base roots hS

end WaveTurbulence.GammaLow.Famc
