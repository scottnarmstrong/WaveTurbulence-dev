/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of rs-src/RedSpliceFinal.lean (FLOWER-P6 R83): only `construction_facts` depends on the changed designations.

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal
import Mathlib.Tactic

/-!
# FLOWER-P6 R83: `construction_facts` for the successor choice data

The successor `NormalizedSplice.collectionChoices` (R83 `hvGroupPick`/`dvGroupPick`) satisfies the same
structural and hinge facts as the original (`structural_collectionChoices`, `hingeOutsideFirst_collectionChoices`
of `VineNormalizedRedSpliceHingePair`). `ladderDataOf` and `SoundBasics` are the original objects (they do not
depend on the designations).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.RedSplice

variable {R : ℕ}

/-- B1b (Mk-general form of `construction_facts`). -/
theorem construction_factsMk (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) {Mk : Set (Stage1.CLVine _)} :
    SoundBasics G (stSt (Mk := Mk) G σ) layer0 p N ∧ (collectionChoices (Mk := Mk) G σ).Structural ∧
      (∀ v ∈ (collectionChoices (Mk := Mk) G σ).hinges, ∀ i,
        ¬ ((collectionChoices (Mk := Mk) G σ).collection i).IsInterior v) := by
  have hno := prime_noTriple G hP
  exact ⟨soundBasics G (unitBlocks (Mk := Mk) G σ) layer0 p N hP.1 hI hbal hn hN hlayer hno,
    structural_collectionChoicesMk (Mk := Mk) (garden_isMolecule G) σ hno, hingeOutsideFirst_collectionChoicesMk (Mk := Mk) σ⟩

/-- **The S2a-owned `Sound` facts of the successor construction.** -/
theorem construction_facts (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) :
    SoundBasics G (stSt G σ) layer0 p N ∧ (collectionChoices G σ).Structural ∧
      (∀ v ∈ (collectionChoices G σ).hinges, ∀ i,
        ¬ ((collectionChoices G σ).collection i).IsInterior v) := construction_factsMk (Mk := ∅) G hP hI hbal hn σ layer0 p N hN hlayer

end WaveTurbulence.VineA.NormalizedSplice
