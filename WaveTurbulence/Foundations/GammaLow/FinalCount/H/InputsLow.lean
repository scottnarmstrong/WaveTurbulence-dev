/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChainLow

/-! # H-LOW's named-input class (PLAN-L6 §3f rule 3; packet L6-HLOW)

`Src.LowInputs`: its only field `chainCoverL : H.ChainCoverLowL'` (`H/FinalCount/LowChainLow.lean`) is the low-range root
form of the LOW chain's ghost step (wt-orch RULING R194). Owner/prover: wt-l6ghost (ghost assembly: M1-R2 Thm 6.1 + Thm 7.1
with L6E's `Ghost.UStep2.excess_low` / `excess_cone` and L6E2's Op-1 cone). L6 merges it into `Src.HInputs` at the gate (I).
Every other named input of the LOW layer is discharged by published proofs: L3's T-vine structure and ladder theorem
(`H.InputsProved`: global `Src.G3Inputs` / `Src.DSInputs` instances), L4's Theorem C. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

/-- **The named inputs of the H-LOW layer** (a `Prop` class: a declaration that needs it adds `[Src.LowInputs]`). -/
class LowInputs : Prop where
  /-- The low-range root form of `chain_coverLL` (RULING R194; prover wt-l6ghost). -/
  chainCoverL : H.ChainCoverLowL'

end WaveTurbulence.GammaLow.FinalCount.Src
