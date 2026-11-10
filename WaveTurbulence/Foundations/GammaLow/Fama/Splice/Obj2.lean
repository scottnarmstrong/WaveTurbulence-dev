/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceObj2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj2


/-!
# REDSPLICE-DEF (S2a), B: the HV object of an SG HVC group in `G_sb`
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- No unit meets an HV group. -/
theorem no_unit_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hhv : ∃ a b, Src.IsHV γ G.molecule S a b)
    (hnhvc : ¬ ∃ a b, Src.IsHVC γ G.molecule S a b)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocks.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [(groupUnitsOf γ G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := partition_eq_maximalGroups (maximalGroupsG_partition (γ := γ) hM)
    have hdisj : (maximalGroupsG γ G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (maximalGroupsG_partition (γ := γ) hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) ((groupUnitsOf γ G S').sub u hu' hv) hvS

/-- (R28) The canonical data `(a, b, e)` of an HV group: its joints and added bond (chosen once, independently of
`σ`); the residual object of `C_1` and the designated object of the group are built from this triple. -/
@[expose] noncomputable def hvPick (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GBranch G.tree × GBranch G.tree × GardenDart G) := by
  classical
  exact if h : ∃ a b, Src.IsHV γ G.molecule S a b then
    some (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose) else none

end WaveTurbulence.GammaLow.Fama
