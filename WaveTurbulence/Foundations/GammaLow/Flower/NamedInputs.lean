/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.P7Late

/-! # FLOWER-LOW (packet L8): named inputs owned by other packets

Each is a `Prop` stated exactly as its source states it; internal theorems take it as a hypothesis under a distinct
name, and wt-orch discharges it at assembly (GH-COMMON "Named inputs").

* `CoupleClauseLowInput` (owner: L7 LG-low, or PLAN-L8 item D from L5a/L5c/L6's gates). TARGET Prop `flowerest1`
  clause (2) (L2290–L2305, "couples"), whose proof (L2306–L2338) uses the layergarden ingredients only: Stage 1,
  finalsbest1/2 and the final count, which for `0 < γ ≤ 1/2` hold over `𝒱_γ` (N3 §4.4 GEN; M2 §8). The Lean form is
  main's couple clause `FlowerTop.CoupleClauseAt` (the couple conjunct of `layergardenFlower_v3`'s body, proved on main
  by `FlowerTop.couple_clause_prefix` for `1/2 < γ`), under `P.γ ≤ 1 / 2`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **Named input (L7 / PLAN-L8 item D).** TARGET `flowerest1` (2) for `0 < γ ≤ 1/2`: the couple clause of the
flower body, `FlowerTop.CoupleClauseAt`, under the flower prefix. -/
def CoupleClauseLowInput : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FlowerTop.CoupleClauseAt P

end WaveTurbulence.GammaLow.Flower
