/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! # H-TV (2): T-vines along main's `FinalCountG3.GroupIso` (packet L6-HTV)

T-analogue (`GroupIso.isVineT`) and low-family form (`GroupIso.isVineS`, `Src.IsSomeVine Src.γL`) of main's
`FinalCountG3.GroupIso.isVine` (`FinalCount/G3GroupIso.lean`), with the same hypotheses. Aliases in main's namespace
`FinalCountG3.GroupIso` give dot notation (`G.isVineT`, `G.isVineS`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H.TV
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V : Type*} [DecidableEq V] {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
  {M : Molecule V D} {S : Finset V} {M' : Molecule V D'} {S' : Finset V} {φ : V → V} {ι : D → D'}

/-- T-analogue of `FinalCountG3.GroupIso.isVine`. -/
theorem GroupIso.isVineT (G : GroupIso M S M' S' φ ι) {j₁ j₂ : V} (hS' : S' ⊆ M'.atoms)
    (hv : M.IsTVine S j₁ j₂) : M'.IsTVine S' (φ j₁) (φ j₂) :=
  isTVine_map_of_groupBonds G.φinj G.img G.groupBonds_eq (G.isBlock hS' hv.1) hv

alias _root_.WaveTurbulence.FinalCountG3.GroupIso.isVineT := GroupIso.isVineT

end WaveTurbulence.GammaLow.FinalCount.H.TV
