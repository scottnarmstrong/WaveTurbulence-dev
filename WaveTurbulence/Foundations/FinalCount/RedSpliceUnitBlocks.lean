/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), A4: the list of units spliced for a prescription

`unitBlocks G σ`: the (CL) blocks to be spliced from the skeleton `G`: the units of every group of
`𝒞 = maximalGroups G.molecule` prescribed SG (TARGET L1953-L1955, `𝒱_0`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ}

/-- The units chosen for the group `S` (empty unless `S` is a group of `𝒞`). -/
noncomputable def groupUnitsOf (G : Garden w) (S : Finset (GBranch G.tree)) : GroupUnits G S := by
  classical
  exact if h : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule then
    Classical.choice (exists_groupUnits h.1 h.2)
  else Classical.choice (groupUnits_empty_nongroup S h)

/-- The finite set of groups of `𝒞`. -/
@[expose] noncomputable def groupsFinset (G : Garden w) : Finset (Finset (GBranch G.tree)) :=
  (Set.toFinite (maximalGroups G.molecule)).toFinset

theorem mem_groupsFinset {G : Garden w} {S : Finset (GBranch G.tree)} :
    S ∈ groupsFinset G ↔ S ∈ maximalGroups G.molecule := by
  simp [groupsFinset]

/-- The SG groups, as a list. -/
@[expose] noncomputable def sgGroups (G : Garden w) (σ : Prescription G) : List (Finset (GBranch G.tree)) :=
  by classical exact (groupsFinset G).toList.filter (fun S => σ S = Molecule.GapKind.SG)

theorem mem_sgGroups {G : Garden w} {σ : Prescription G} {S : Finset (GBranch G.tree)} :
    S ∈ sgGroups G σ ↔ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG := by
  classical
  simp [sgGroups, mem_groupsFinset]

/-- **The units spliced for the prescription `σ`** (the (CL) vine chains of `𝒱_0`, TARGET L1953-L1955). -/
noncomputable def unitBlocks (G : Garden w) (σ : Prescription G) : List (CLBlock G) :=
  (sgGroups G σ).flatMap (fun S => (groupUnitsOf G S).units)

theorem mem_unitBlocks {G : Garden w} {σ : Prescription G} {u : CLBlock G} :
    u ∈ unitBlocks G σ ↔ ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      u ∈ (groupUnitsOf G S).units := by
  simp only [unitBlocks, List.mem_flatMap, mem_sgGroups]
  constructor
  · rintro ⟨S, ⟨h1, h2⟩, h3⟩; exact ⟨S, h1, h2, h3⟩
  · rintro ⟨S, h1, h2, h3⟩; exact ⟨S, ⟨h1, h2⟩, h3⟩

theorem unitBlocks_pairwise {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G) :
    (unitBlocks G σ).Pairwise (fun u u' => Disjoint u.atoms u'.atoms) := by
  classical
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
    have := (stage1Collection_isPartition hM).2.1
    rwa [hpart] at this
  unfold unitBlocks
  rw [List.pairwise_flatMap]
  refine ⟨fun S _ => (groupUnitsOf G S).disj, ?_⟩
  have hnd : (sgGroups G σ).Nodup := (Finset.nodup_toList _).filter _
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro S T hS hT hne u hu u' hu'
  have hSm := (mem_sgGroups.mp hS).1
  have hTm := (mem_sgGroups.mp hT).1
  exact (hdisj hSm hTm hne).mono ((groupUnitsOf G S).sub u hu) ((groupUnitsOf G T).sub u' hu')

/-- Every atom of a unit lies in a vine of `𝒱_0` contained in the unit. -/
theorem unitBlocks_sound {G : Garden w} {σ : Prescription G} {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    ∀ v ∈ u.atoms, ∃ c ∈ vinesV0 G σ, v ∈ c.atoms ∧ c.atoms ⊆ u.atoms := by
  obtain ⟨S, hSm, hσ, hu⟩ := mem_unitBlocks.mp hu
  obtain ⟨cs, hcs, hiff⟩ := (groupUnitsOf G S).sound u hu
  intro v hv
  obtain ⟨c, hc, hvc⟩ := (hiff v).mp hv
  obtain ⟨c', hc'V, hc'a, hc'i⟩ := hcs c hc
  refine ⟨c', ⟨hc'V, S, hSm, hc'a ▸ hc'i, hσ⟩, hc'a ▸ hvc, ?_⟩
  intro z hz
  exact (hiff z).mpr ⟨c, hc, hc'a ▸ hz⟩

end WaveTurbulence.RedSplice
