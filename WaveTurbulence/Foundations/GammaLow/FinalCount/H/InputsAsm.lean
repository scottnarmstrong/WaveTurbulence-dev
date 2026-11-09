/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChainLow

/-! # H-ASM / H-GARDEN (packet L6-HASM): the layer's named inputs

`class Src.AsmInputs` (PLAN-L6 §3f rule 3): the named inputs used by the layers H-ASM and H-GARDEN, as a `Prop` class
so that instance resolution threads them; L6 merges it into `Src.HInputs` at the gate. Its only field is the ghost step
(wt-orch DECISION on the STOPPED item of H-ASM-PROGRESS):
* `chainCover`: the low-range `chain_cover`, root form (`H.ChainCoverLow'`, `FinalCount/AsmChainLow.lean`; wt-orch
  RULING R194 = wt-l6ghost's corrected field): main's `FinalCountAsm.chain_cover` with `h8 : 8η ≤ 2γ − 1` deleted,
  the conclusion at the initial state only, the Op-1 creation cone `hExC : Ex1Cone …` (`FinalCount/AsmEx1Cone.lean`),
  the (f′) split budget `Ks = 2·|atoms M₀| + 1` in `hNC1'`/`hNC2'`, and the charged-step constant `ghostConstChain`
  (`≥ Ghost.ghostConstLow`, `≥ 9·25^d · ghostConst`). Truth: M1-R2 Thm 6.1 + 7.1 (root telescoping). Prover:
  wt-l6ghost.

Former fields, now proved and used directly: N2 Lemma 5.2 (L3, `TVine.Struct.Drawn.drawnTVine`, in `AsmProp96Low`);
L4's Theorem C (`TVine.Chart.tvineChartExists_holds`, in `AsmEx1ULow`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.Src

/-- **The named inputs of the layers H-ASM and H-GARDEN.** -/
class AsmInputs : Prop where
  /-- The ghost step of the REG chain at `γ ≤ 1/2` (M1-R2 Thm 6.1 + 7.1; prover wt-l6ghost). -/
  chainCover : H.ChainCoverLow'

end WaveTurbulence.GammaLow.FinalCount.Src
