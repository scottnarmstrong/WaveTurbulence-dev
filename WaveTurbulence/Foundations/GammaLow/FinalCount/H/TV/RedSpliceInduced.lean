/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceInduced
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! # H-TV (2): T-vines along main's `RedSplice.InducedIso` (packet L6-HTV)

T-analogue (`InducedIso.isVineT`) and low-family form (`InducedIso.isVineS`, `Src.IsSomeVine Src.γL`) of main's
`RedSplice.InducedIso.isVine` (`FinalCount/RedSpliceInduced.lean`), with the same hypotheses. Aliases in main's
namespace `RedSplice.InducedIso` give dot notation (`I.isVineT`, `I.isVineS`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.TV
open Finset WaveTurbulence WaveTurbulence.RedSplice

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {M : Molecule V D} {M' : Molecule V' D'} {B : Finset V} {B' : Finset V'}

/-- T-analogue of `RedSplice.InducedIso.isVine`. -/
theorem InducedIso.isVineT (I : InducedIso M M' B B') {a b : V} (hV : M.IsTVine B a b) :
    M'.IsTVine B' (I.π a) (I.π b) :=
  isTVine_map_of_groupBonds I.inj I.img.symm I.groupBonds_map (I.isBlock hV.1) hV

/-- Low-family form of `RedSplice.InducedIso.isVine` (main's lemma at (I), (II), and `InducedIso.isVineT`). -/
theorem InducedIso.isVineS (I : InducedIso M M' B B') {a b : V} (hV : Src.IsSomeVine Src.γL M B a b) :
    Src.IsSomeVine Src.γL M' B' (I.π a) (I.π b) := by
  rcases hV.cases with h | h | h
  · exact Src.isSomeVine_of_I (I.isVine h)
  · exact Src.isSomeVine_of_II (I.isVine h)
  · exact Src.isSomeVine_of_T (InducedIso.isVineT I h)

alias _root_.WaveTurbulence.RedSplice.InducedIso.isVineT := InducedIso.isVineT
alias _root_.WaveTurbulence.RedSplice.InducedIso.isVineS := InducedIso.isVineS

end WaveTurbulence.GammaLow.FinalCount.H.TV
