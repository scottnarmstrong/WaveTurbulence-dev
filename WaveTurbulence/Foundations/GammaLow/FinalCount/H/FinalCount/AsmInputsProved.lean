/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsAsm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLow

/-! # The named inputs of H-ASM / H-GARDEN, discharged (packet L6-HASM)

The only field of `Src.AsmInputs`, the low-range ghost step `H.ChainCoverLow'` (wt-orch DECISION + RULING R194, form
agreed with wt-l6ghost), is proved by wt-l6ghost: `Ghost.chainCoverLow'_holds` (module `Ghost.ChainLow`; standard
axioms). So `Src.AsmInputs` has a global instance (the pattern of L6's `H.InputsProved` for `Src.G3Inputs`,
`Src.DSInputs`). `AsmTopClass3` imports this module, so `reg_class_bound` and everything above it (`AsmRegMol`,
`AsmGReg2`, `AsmPrefix`) are stated without `[Src.AsmInputs]`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

/-- H-ASM's input class, discharged by wt-l6ghost's proof of the low-range `chain_cover`. -/
instance asmInputs_proved : AsmInputs := ⟨Ghost.chainCoverLow'_holds⟩

end WaveTurbulence.GammaLow.FinalCount.Src
