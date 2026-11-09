/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenUnloop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenUnloop`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): `LowClassHyps2` on `M.unloop`.**

`lowClassHyps2_unloop`: from the data on a molecule `M` with at least one loop (the `LowLoopData` of the garden-level facts of the
REG producers, which hold with loops) every field of `LowClassHyps2` holds on `M.unloop` with index `R + k`, collection
`C.unloop`, omitted vines `unloopSet`, first-stage set `unloopSet M Fst`, for every nonempty class of `unloopAdm M Adm`.
The new `degen` field `DegenSGTL`: an atom with a loop and a zero-gap pair on `M.unloop` has degree 2, equal labels (`heq`), so
it is a `SmoothAt` atom; atoms without a loop keep their degree, so `M`-tame is `M.unloop`-tame. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section gen
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem lift_shape_vc {M : Molecule V D} (P' : Src.Object Src.γL M.unloop) (hlf : LoopFreeSet M P'.atoms)
    (h : ∃ h, P'.shape = Src.VineLikeObject.vc h) : ∃ h, (P'.lift hlf).shape = Src.VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := P'
  cases sh with
  | vc hv => exact ⟨_, rfl⟩
  | hyper R => obtain ⟨h, hh⟩ := h; cases hh

theorem unloop_shape_vc' {M : Molecule V D} (U : Src.Object Src.γL M) (hU : LoopFreeSet M U.atoms)
    (h : ∃ h, (U.unloop hU).shape = Src.VineLikeObject.vc h) : ∃ h, U.shape = Src.VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc hv => exact ⟨_, rfl⟩
  | hyper R => obtain ⟨h, hh⟩ := h; cases hh

end gen

end WaveTurbulence.GammaLow.FinalCount.H
