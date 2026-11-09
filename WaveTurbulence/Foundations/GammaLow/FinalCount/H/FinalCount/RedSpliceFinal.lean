/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceFinal`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): the construction `G_sb`, `C_1`, hinges, ladders (assembly of the facts)

For a prime irreducible skeleton `G` of width `2R` and a prescription `σ`, `gsbOf G σ = stSt G σ` is the
skeleton with all units of `𝒱_0` spliced, `collectionChoices G σ` its choice data, `ladderDataOf` the selected
ladder presentations, and `construction_facts` collects every `Sound` field that S2a owns.
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {R : ℕ}

/-- B1b (Mk-general form of `construction_facts`). -/
theorem construction_factsMk (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) {Mk : Set (CLVine _)} :
    SoundBasics G (stSt (Mk := Mk) G σ) layer0 p N ∧ (collectionChoices (Mk := Mk) G σ).Structural ∧
      (∀ v ∈ (collectionChoices (Mk := Mk) G σ).hinges, ∀ i,
        ¬ ((collectionChoices (Mk := Mk) G σ).collection i).IsInterior v) := by
  have hno := prime_noTriple G hP
  exact ⟨soundBasics G (unitBlocks (Mk := Mk) G σ) layer0 p N hP.1 hI hbal hn hN hlayer hno,
    structural_collectionChoicesMk (Mk := Mk) (garden_isMolecule G) σ hno, hingeOutsideFirst_collectionChoicesMk (Mk := Mk) σ⟩

/-- **The S2a-owned `Sound` facts of the construction.** -/
theorem construction_facts (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) :
    SoundBasics G (stSt G σ) layer0 p N ∧ (collectionChoices G σ).Structural ∧
      (∀ v ∈ (collectionChoices G σ).hinges, ∀ i,
        ¬ ((collectionChoices G σ).collection i).IsInterior v) := construction_factsMk (Mk := ∅) G hP hI hbal hn σ layer0 p N hN hlayer

end WaveTurbulence.GammaLow.FinalCount.H
