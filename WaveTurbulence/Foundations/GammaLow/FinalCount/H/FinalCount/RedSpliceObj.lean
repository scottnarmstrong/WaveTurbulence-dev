/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSkip
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceObj`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a), B: the objects of `C_1` in `G_sb`

Constructors of `SourceVine.Object` from a vine of the spliced molecule (`.vc`) or from a vine of an adjoint
(`.hyper`), and the transport of the skipped vine of an SG group (and of an SG HV group) into `G_sb`.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- An `.vc` object from a vine. -/
@[expose] def objVC {G : Garden w} (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (h : Src.IsSomeVine Src.γL G.molecule A u l) : Src.Object Src.γL G.molecule :=
  ⟨A, u, l, .vc ⟨h.block, 1, Src.Chain.single h⟩⟩

/-- A `.hyper` object from a vine of the adjoint. -/
@[expose] def objHyper {G : Garden w} (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Src.IsSomeVine Src.γL (Mole.eraseBond G.molecule e) A u l) :
    Src.Object Src.γL G.molecule :=
  ⟨A, u, l, .hyper ⟨e, hends, ⟨h.block, 1, Src.Chain.single h⟩⟩⟩

theorem allowed_hyper {G : Garden w} (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Src.IsSomeVine Src.γL (Mole.eraseBond G.molecule e) A u l) :
    Src.AllowedCollectionObject Src.γL G (objHyper e A u l hends h) := h

end WaveTurbulence.GammaLow.FinalCount.H
