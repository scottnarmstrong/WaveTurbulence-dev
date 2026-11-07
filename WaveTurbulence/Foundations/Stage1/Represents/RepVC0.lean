/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.Align.Export
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG15
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 11: aligned assembly (probe)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA WaveTurbulence.VineEstS4

variable {w : ℕ} {S : Garden w}

/-- The aligned assembly has the same chain lengths and regions as the producer's unit assembly. -/
noncomputable abbrev unitAssemblyAl (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    CLChainAssembly S (regionOf (unitBlk hM σ j)) (unitN σ j) := VineAlign.alignedAssembly hM σ j

end WaveTurbulence.Represents
