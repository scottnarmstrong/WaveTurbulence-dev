/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceFinal` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.FinalCount.RedSpliceNoTriple
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSound
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal


/-!
# REDSPLICE-DEF (S2a): the construction `G_sb`, `C_1`, hinges, ladders (assembly of the facts)

For a prime irreducible skeleton `G` of width `2R` and a prescription `σ`, `gsbOf γ G σ = stSt γ G σ` is the
skeleton with all units of `𝒱_0` spliced, `collectionChoices γ G σ` its choice data, `ladderDataOf` the selected
ladder presentations, and `construction_facts` collects every `Sound` field that S2a owns.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount

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

variable {R : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `construction_facts`). -/
theorem construction_factsMk (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) {Mk : Set (CLVineG γ _)} :
    SoundBasics G (stSt γ (Mk := Mk) G σ) layer0 p N ∧ (collectionChoices γ (Mk := Mk) G σ).Structural ∧
      (∀ v ∈ (collectionChoices γ (Mk := Mk) G σ).hinges, ∀ i,
        ¬ ((collectionChoices γ (Mk := Mk) G σ).collection i).IsInterior v) := by
  have hno := prime_noTriple G hP
  exact ⟨soundBasics G (unitBlocks γ (Mk := Mk) G σ) layer0 p N hP.1 hI hbal hn hN hlayer hno,
    structural_collectionChoicesMk (Mk := Mk) (garden_isMolecule G) σ hno, hingeOutsideFirst_collectionChoicesMk (Mk := Mk) σ⟩

/-- **The S2a-owned `Sound` facts of the construction.** -/
theorem construction_facts (G : Garden (2 * R)) (hP : Reg.Skeleton.IsPrimeGarden G) (hI : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (p N : ℕ) (hN : G.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p) :
    SoundBasics G (stSt γ G σ) layer0 p N ∧ (collectionChoices γ G σ).Structural ∧
      (∀ v ∈ (collectionChoices γ G σ).hinges, ∀ i,
        ¬ ((collectionChoices γ G σ).collection i).IsInterior v) := construction_factsMk (Mk := ∅) G hP hI hbal hn σ layer0 p N hN hlayer

end WaveTurbulence.GammaLow.Fama
