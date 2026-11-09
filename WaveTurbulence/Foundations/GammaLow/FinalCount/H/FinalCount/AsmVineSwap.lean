/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # H-ASM (packet L6-HASM): joint symmetry of the low family

Main's `FinalCountAsm.isVine_orient` (`FinalCount/AsmVN13.lean`) for the drawn types, extended to the low family
(I), (II), T-vines through the Api's `Src.IsSomeVine.swap`, for the ported `AsmVN13` (`singleVineVC_of_objVine`, whose
objects are members of `𝒱_{γL}` read through the state isomorphism): `isSomeVine_orient`,
`isSomeVine_atoms_congr`, `isSomeVine_eraseBond_congr`. (The family swap itself is the Api's; H-MS's
`Spine.SourceChainSwap.isSomeVine_swap` is the same statement.) -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.H

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {N : Molecule V D}

/-- Low-family form of main's `isVine_orient`. -/
theorem isSomeVine_orient {S : Finset V} {u l p q : V} (hpq : p ≠ q) (h : ({p, q} : Finset V) = {u, l})
    (hv : Src.IsSomeVine Src.γL N S u l) : Src.IsSomeVine Src.γL N S p q := by
  rcases WaveTurbulence.FinalCountAsm.joints_cases hpq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hv
  · exact Src.IsSomeVine.swap hv

theorem isSomeVine_atoms_congr {S S' : Finset V} {a b : V} (h : S = S') (hv : Src.IsSomeVine Src.γL N S a b) :
    Src.IsSomeVine Src.γL N S' a b := h ▸ hv

theorem isSomeVine_eraseBond_congr {e e' : D} (he : e = e') {S : Finset V} {a b : V}
    (hv : Src.IsSomeVine Src.γL (N.eraseBond e) S a b) : Src.IsSomeVine Src.γL (N.eraseBond e') S a b := he ▸ hv

end WaveTurbulence.GammaLow.FinalCount.H
