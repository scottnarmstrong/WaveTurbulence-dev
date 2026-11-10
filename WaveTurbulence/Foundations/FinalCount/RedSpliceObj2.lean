/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), B: the HV object of an SG HVC group in `G_sb`
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- No unit meets an HV group. -/
theorem no_unit_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hhv : ∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b)
    (hnhvc : ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocks.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [(groupUnitsOf G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
    have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (stage1Collection_isPartition hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) ((groupUnitsOf G S').sub u hu' hv) hvS

/-- (R28) The canonical data `(a, b, e)` of an HV group: its joints and added bond (chosen once, independently of
`σ`); the residual object of `C_1` and the designated object of the group are built from this triple. -/
@[expose] noncomputable def hvPick (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GBranch G.tree × GBranch G.tree × GardenDart G) := by
  classical
  exact if h : ∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b then
    some (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose) else none

end WaveTurbulence.RedSplice
