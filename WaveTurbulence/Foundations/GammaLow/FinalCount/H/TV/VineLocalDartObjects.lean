/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLocalDartObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! # H-TV (2): T-vines under local dart identifications (packet L6-HTV)

T-analogue (`LocalDartEmbedding.isVine_iffT`) and low-family form (`LocalDartEmbedding.isVine_iffS`,
`Src.IsSomeVine Src.γL`) of main's `Vine.LocalDartEmbedding.isVine_iff` (`Molecule/VineLocalDartObjects.lean`), with
the same hypotheses (the vine type argument `X` is dropped). Aliases in main's namespace `Vine.LocalDartEmbedding`
give dot notation (`F.isVine_iffT`, `F.isVine_iffS`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.TV
open Finset WaveTurbulence WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}

/-- T-analogue of `Vine.LocalDartEmbedding.isVine_iff`. -/
theorem LocalDartEmbedding.isVine_iffT (F : LocalDartEmbedding M N A) (S : Finset V) (hSA : S ⊆ A) (a b : V) :
    N.IsTVine S a b ↔ M.IsTVine S a b := by
  classical
  exact isTVine_iff_of_groupBonds_eq (F.groupBonds_eq S hSA) (F.isBlock_iff S hSA a b)

/-- Low-family form of `Vine.LocalDartEmbedding.isVine_iff` (main's lemma at (I), (II), and
`LocalDartEmbedding.isVine_iffT`). -/
theorem LocalDartEmbedding.isVine_iffS (F : LocalDartEmbedding M N A) (S : Finset V) (hSA : S ⊆ A) (a b : V) :
    Src.IsSomeVine Src.γL N S a b ↔ Src.IsSomeVine Src.γL M S a b := by
  classical
  rw [Src.isSomeVine_γL_iff, Src.isSomeVine_γL_iff, Molecule.IsVineEnl, Molecule.IsVineEnl,
    F.isVine_iff .I S hSA a b, F.isVine_iff .II S hSA a b, LocalDartEmbedding.isVine_iffT F S hSA a b]

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.isVine_iffT := LocalDartEmbedding.isVine_iffT
alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.isVine_iffS := LocalDartEmbedding.isVine_iffS

end WaveTurbulence.GammaLow.FinalCount.H.TV
