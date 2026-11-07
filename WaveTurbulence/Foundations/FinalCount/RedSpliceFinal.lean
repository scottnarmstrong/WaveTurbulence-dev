/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.FinalCount.RedSpliceNoTriple
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSound
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the construction `G_sb`, `C_1`, hinges, ladders (assembly of the facts)

For a prime irreducible skeleton `G` of width `2R` and a prescription `σ`, `gsbOf G σ = stSt G σ` is the
skeleton with all units of `𝒱_0` spliced, `collectionChoices G σ` its choice data, `ladderDataOf` the selected
ladder presentations, and `construction_facts` collects every `Sound` field that S2a owns.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine

/-- The selected presentation of each maximal ladder of a garden molecule. -/
noncomputable def ladderDataOf {w : ℕ} (G : Garden w) : SourceMaximalLadderData G :=
  have h : ∀ S : {S // S ∈ G.molecule.maximalLadders}, ∃ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree),
      G.molecule.IsLadder u v ∧ Molecule.ladderAtoms u v = S.1 := by
    intro S
    have h2 : S.1 ⊆ G.molecule.atoms ∧ G.molecule.IsLadderSet S.1 ∧
        ∀ S' : Finset (GBranch G.tree), G.molecule.IsLadderSet S' → S.1 ⊆ S' → S' = S.1 := by
      simpa [Molecule.maximalLadders] using S.2
    exact h2.2.1
  { length := fun S => (h S).choose
    upper := fun S => (h S).choose_spec.choose
    lower := fun S => (h S).choose_spec.choose_spec.choose
    ladder := fun S => (h S).choose_spec.choose_spec.choose_spec.1
    atoms := fun S => (h S).choose_spec.choose_spec.choose_spec.2 }

variable {R : ℕ}

/-- **The S2a-owned `Sound` facts of the construction.** -/
theorem construction_facts (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) :
    SoundBasics G (stSt G σ) layer0 p N ∧ (collectionChoices G σ).Structural ∧
      (∀ v ∈ (collectionChoices G σ).hinges, ∀ i,
        ¬ ((collectionChoices G σ).collection i).IsInterior v) := by
  have hno := prime_noTriple G hP
  exact ⟨soundBasics G (unitBlocks G σ) layer0 p N hP.1 hI hbal hn hN hlayer hno,
    structural_collectionChoices (garden_isMolecule G) σ hno, hingeOutsideFirst_collectionChoices σ⟩

end WaveTurbulence.RedSplice
