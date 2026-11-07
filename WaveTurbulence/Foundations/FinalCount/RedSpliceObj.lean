/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkip
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), B: the objects of `C_1` in `G_sb`

Constructors of `SourceVine.Object` from a vine of the spliced molecule (`.vc`) or from a vine of an adjoint
(`.hyper`), and the transport of the skipped vine of an SG group (and of an SG HV group) into `G_sb`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- An `.vc` object from a vine. -/
@[expose] def objVC {G : Garden w} (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (h : Vine.IsSomeVine G.molecule A u l) : Object G.molecule :=
  ⟨A, u, l, .vc ⟨h.choose_spec.1, 1, Chain.single h⟩⟩

/-- A `.hyper` object from a vine of the adjoint. -/
@[expose] def objHyper {G : Garden w} (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Vine.IsSomeVine (Mole.eraseBond G.molecule e) A u l) :
    Object G.molecule :=
  ⟨A, u, l, .hyper ⟨e, hends, ⟨h.choose_spec.1, 1, Chain.single h⟩⟩⟩

theorem allowed_hyper {G : Garden w} (e : GardenDart G) (A : Finset (GBranch G.tree)) (u l : GBranch G.tree)
    (hends : G.molecule.ends e = s(u, l)) (h : Vine.IsSomeVine (Mole.eraseBond G.molecule e) A u l) :
    AllowedCollectionObject G (objHyper e A u l hends h) := h

end WaveTurbulence.RedSplice
