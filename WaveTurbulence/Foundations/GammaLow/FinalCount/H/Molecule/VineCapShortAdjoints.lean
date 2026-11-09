/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineCapShortAdjoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineCapShortAdjoints`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # The zero-rung cap adjoint is a double chain; one/two-rung caps are not vine-like

**Low-range change (L6-HMS2, FINDINGS F1 in `H/H-MS2-PROGRESS.md`).** Main's `CapPrefixData.short_prefix_not_hyperLike`
(a cap with `r = 1` or `r = 2` selected full rungs is neither HV nor HVC) is **false** in the low family and is not
ported: the five-atom (`r = 1`) and seven-atom (`r = 2`) cap adjoints are T-vines (their closures are, resp. reduce by one
(Y2) step to, the doubled triangle), so such a cap is an HV of `𝒱_{γL}`. It has no consumer in the ported run (H-DS's
cap classification `hyper_realization_in_vine` already allows a T-vine adjoint). -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
open WaveTurbulence.Vine.CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

include C in
/-- A triangle-only hyper-vine-like cap has exactly the source two-double-
bond adjoint. The designated actual deleted bond is retained. -/
theorem zero_prefix_adjoint_doubleChainL {x y : V} (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y)
    (hr : r=0) : ∃ e : D,M.ends e=s(x,y) ∧ DoubleChain (Mole.eraseBond M e) A x y 2 := by
  apply hyperLike_three_atom_adjoint h
  have hc := C.card_atoms
  omega

alias _root_.WaveTurbulence.Vine.CapPrefixData.zero_prefix_adjoint_doubleChainL := _root_.WaveTurbulence.GammaLow.FinalCount.H.CapPrefixData.zero_prefix_adjoint_doubleChainL
end CapPrefixData
end WaveTurbulence.GammaLow.FinalCount.H
