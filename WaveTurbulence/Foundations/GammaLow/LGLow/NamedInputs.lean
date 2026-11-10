/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Gate
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt

/-! # LG-low (packet L07): finalsbest2 over `𝒱_γ`, and the remaining named input

* **`FineSplicedGammaInput`**: TARGET finalsbest2 (L2078) for the spliced kernel of `𝒱_γ` choice data, for
  `0 < γ ≤ 1/2`, from finalcount1 over `𝒱_γ` (L2114–L2116, L6's `FinalCountGammaAt`) and ladderl1old (L1994–L2001,
  main's `LadderFourierAt`) through the counting cover (L2097–L2116). Main proves the drawn-family statement as
  `LGSpine.Cover.fine_spliced_of_subpro_choices`, which `LGSpine.stage1_piece_bound_int` interpolates with
  finalsbest1; the `𝒱_γ` piece bound of this packet does the same with L5c's `Famc.CoarseSplicedGammaAt` and this
  statement (FINDINGS F1). The shape is L5c's (`Famc.Defs`: `FineSplicedChoicesGammaAt`, `CoverSmall`).
* **`fineSplicedGammaInput_of_subObjects`**: it is PROVED from L5c's `Famc.fineSplicedChoicesGamma`
  (`Famc/Cover/Gate.lean`, all `0 < γ < 1`), whose only hypothesis is the named input `Famc.SubObjectsInput`
  (= L3's `TVine.Struct.SubObjectsStatement.{0,0}`, N2 Theorem 1.15 (F1)). That is the only named input of LG-low and
  of the couple clause besides the three low gates. -/
@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.LGSpine

/-- **TARGET finalsbest2 (L2078) over `𝒱_γ`, for `0 < γ ≤ 1/2`**, from finalcount1 over
`𝒱_γ` and ladderl1old through the counting cover (L2097–L2116): the shape of L5c's planned
`Famc.fineSplicedChoicesGamma` (PLAN-L5c §1), i.e. main's `Cover.fine_spliced_of_subpro_choices` with the `𝒱_γ`
choice data `FinalCount.Src.SubproChoices P.γ`. -/
def FineSplicedGammaInput : Prop :=
  ∀ P : WTParams, P.γ ≤ 1 / 2 → LadderFourierAt P → FinalCount.FinalCountGammaAt P → Famc.CoverSmall P →
    Famc.FineSplicedChoicesGammaAt P

/-- `FineSplicedGammaInput` from L5c's `Famc.fineSplicedChoicesGamma` (which needs no restriction on `γ`), given
L3's `SubObjectsInput`. -/
theorem fineSplicedGammaInput_of_subObjects (hSO : Famc.SubObjectsInput) : FineSplicedGammaInput :=
  fun P _ hfourier hcount hs => Famc.fineSplicedChoicesGamma hSO P hfourier hcount hs

end WaveTurbulence.GammaLow.LGLow
