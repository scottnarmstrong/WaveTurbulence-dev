/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproShapeC1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproShapeC1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-SHAPE goal 1: every object of `C₁` is single-vine classified (`hC1vine`)

TARGET `subpro` (2) (L2043): each object of `C₁` is an SG HV, an SG (CN) vine or an SG root (CL) vine. S2a's construction records
this as `AllowedCollectionObject` (`ObjSpec.allowed`, `structural_collectionChoices`): a vc-shaped object is `IsSomeVine` in the
molecule, a hyper-shaped one is `IsSomeVine` in the adjoint of its designated bond. That is exactly the assembly's `ObjVine`.
A vine has at least four atoms, so the `U.atoms.card = 3` branch of the assembly's shape hypothesis never occurs for `C₁`.
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountAsm

variable {w : ℕ}

/-- An allowed collection object (TARGET `subpro` (2)) is `ObjVine` at the molecule of its garden. -/
theorem objVine_of_allowed {G : Garden w} {U : Src.Object Src.γL G.molecule} (h : Src.AllowedCollectionObject Src.γL G U) :
    ObjVine G.molecule U := by
  unfold ObjVine
  unfold Src.AllowedCollectionObject at h
  rcases hs : U.shape with h0 | R
  · rw [hs] at h
    exact Src.isSomeVine_γL_iff.mp h.1
  · rw [hs] at h
    exact Src.isSomeVine_γL_iff.mp h

/-- A vine has at least four atoms or is a double bond (two atoms): an object classified by `ObjVine` never has exactly three atoms. -/
theorem objVine_card_ne_three {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀]
    {M : Molecule V D₀} {U : Src.Object Src.γL M} (h : ObjVine M U) : U.atoms.card ≠ 3 := by
  intro h3
  unfold ObjVine at h
  rcases hs : U.shape with h0 | R
  · rw [hs] at h
    have hX : Src.IsSomeVine Src.γL _ U.atoms U.upper U.lower := Src.isSomeVine_γL_iff.mpr h
    have hI := RS.isSomeVine_typeI_of_card_lt_four hX (by omega)
    have := Vine.typeI_atoms hI
    rw [this, Finset.card_pair hX.block.2.2.2.1] at h3
    omega
  · rw [hs] at h
    have hX : Src.IsSomeVine Src.γL _ U.atoms U.upper U.lower := Src.isSomeVine_γL_iff.mpr h
    have hI := RS.isSomeVine_typeI_of_card_lt_four hX (by omega)
    have := Vine.typeI_atoms hI
    rw [this, Finset.card_pair hX.block.2.2.2.1] at h3
    omega

end WaveTurbulence.GammaLow.FinalCount.H
