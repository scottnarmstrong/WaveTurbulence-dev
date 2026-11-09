/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceObj` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj


/-!
# REDSPLICE-DEF (S2a), B: the objects of `C_1` in `G_sb`

Constructors of `Src.Object γ` from a vine of the spliced molecule (`.vc`) or from a vine of an adjoint
(`.hyper`), and the transport of the skipped vine of an SG group (and of an SG HV group) into `G_sb`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

/-- An `.vc` object from a vine. -/
@[expose] def objVC {G : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (h : Src.IsSomeVine γ G.molecule A u l) : Src.Object γ G.molecule :=
  ⟨A, u, l, .vc ⟨(Src.isBlock_of_isSomeVine h), 1, Src.Chain.single h⟩⟩

/-- A `.hyper` object from a vine of the adjoint. -/
@[expose] def objHyper {G : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Src.IsSomeVine γ (Mole.eraseBond G.molecule e) A u l) :
    Src.Object γ G.molecule :=
  ⟨A, u, l, .hyper ⟨e, hends, ⟨(Src.isBlock_of_isSomeVine h), 1, Src.Chain.single h⟩⟩⟩

theorem allowed_hyper {G : Garden w} (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Src.IsSomeVine γ (Mole.eraseBond G.molecule e) A u l) :
    Src.AllowedCollectionObject γ G (objHyper γ e A u l hends h) := h

end WaveTurbulence.GammaLow.Fama
