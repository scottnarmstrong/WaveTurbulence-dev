/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0
public import WaveTurbulence.Foundations.FinalCount.RedSpliceMarked
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), A4: the list of units spliced for a prescription

`unitBlocks G σ`: the (CL) blocks to be spliced from the skeleton `G`: the units of every group of
`𝒞 = maximalGroups G.molecule` prescribed SG (TARGET L1953-L1955, `𝒱_0`).

B1a (ruling F-1): `unitBlocks G σ Mk` takes the trailing marked vine set `Mk` (default `∅`); the units of a group are
`groupUnitsMk G Mk S` (main's units for an unmarked group, the runs for a marked one).  At `∅` they are main's
(`groupUnitsMk_empty`, `unitBlocks_empty`).  The Mk-general API is `mem_unitBlocksMk`, `unitBlocks_pairwiseMk`,
`unitBlocks_soundMk`; the probe's `unitBlocksMk` and `survivorsMk` are added with their `∅`-bridges.
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

/-- B1a. The units of one SG group: main's units for an unmarked group, the runs for a marked one (copied by source
from the B0 probe, lines 166–173). -/
noncomputable def groupUnitsMk (G : Garden w) (Mk : Set (Stage1.CLVine G)) (S : Finset (GBranch G.tree)) :
    List (CLBlock G) := by
  classical
  exact if markedGroup G Mk S then
    (if h : Nonempty (MarkedGroupUnits G S Mk) then (Classical.choice h).runs else [])
  else (groupUnitsOf G S).units

/-- B1a bridge: at `Mk = ∅` the units of a group are main's. -/
theorem groupUnitsMk_empty (G : Garden w) (S : Finset (GBranch G.tree)) :
    groupUnitsMk G ∅ S = (groupUnitsOf G S).units := by
  simp [groupUnitsMk, markedGroup]

/-- The units of an unmarked group are main's. -/
theorem groupUnitsMk_of_not_marked {G : Garden w} {Mk : Set (Stage1.CLVine G)} {S : Finset (GBranch G.tree)}
    (h : ¬ markedGroup G Mk S) : groupUnitsMk G Mk S = (groupUnitsOf G S).units := by
  classical
  unfold groupUnitsMk
  simp only [h, ↓reduceIte]

/-- The units of a group lie in the group. -/
theorem groupUnitsMk_sub {G : Garden w} {Mk : Set (Stage1.CLVine G)} {S : Finset (GBranch G.tree)}
    {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S) : u.atoms ⊆ S := by
  classical
  unfold groupUnitsMk at hu
  split_ifs at hu with h1 h2
  · exact (Classical.choice h2).sub u hu
  · simp at hu
  · exact (groupUnitsOf G S).sub u hu

/-- The units of a group are pairwise disjoint. -/
theorem groupUnitsMk_disj (G : Garden w) (Mk : Set (Stage1.CLVine G)) (S : Finset (GBranch G.tree)) :
    (groupUnitsMk G Mk S).Pairwise (fun u u' => Disjoint u.atoms u'.atoms) := by
  classical
  unfold groupUnitsMk
  split_ifs with h1 h2
  · exact (Classical.choice h2).disj
  · exact List.Pairwise.nil
  · exact (groupUnitsOf G S).disj

/-- Every unit of a group is a union of unmarked `𝒱`-ingredients of the group. -/
theorem groupUnitsMk_sound {G : Garden w} {Mk : Set (Stage1.CLVine G)} {S : Finset (GBranch G.tree)}
    {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S) : ∃ cs : List (Stage1.CLVine G),
      (∀ c ∈ cs, c ∈ Stage1.vinesV G ∧ c ∉ Mk ∧ Stage1.IsIngredient G.molecule S c.atoms) ∧
      ∀ v, v ∈ u.atoms ↔ ∃ c ∈ cs, v ∈ c.atoms := by
  classical
  unfold groupUnitsMk at hu
  split_ifs at hu with h1 h2
  · exact (Classical.choice h2).sound u hu
  · simp at hu
  · obtain ⟨cs, hcs, hiff⟩ := (groupUnitsOf G S).sound u hu
    choose f hf using hcs
    refine ⟨cs.attach.map fun c => f c.1 c.2, ?_, ?_⟩
    · intro c hc
      obtain ⟨⟨c0, hc0⟩, -, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hV, ha, hI⟩ := hf c0 hc0
      have hI' : Stage1.IsIngredient G.molecule S (f c0 hc0).atoms := by rw [ha]; exact hI
      exact ⟨hV, not_mem_of_not_markedGroup h1 hV hI', hI'⟩
    · intro v
      rw [hiff v]
      constructor
      · rintro ⟨c0, hc0, hv⟩
        refine ⟨f c0 hc0, List.mem_map.mpr ⟨⟨c0, hc0⟩, List.mem_attach _ _, rfl⟩, ?_⟩
        rw [(hf c0 hc0).2.1]; exact hv
      · rintro ⟨c, hc, hv⟩
        obtain ⟨⟨c0, hc0⟩, -, rfl⟩ := List.mem_map.mp hc
        refine ⟨c0, hc0, ?_⟩
        rw [← (hf c0 hc0).2.1]; exact hv

/-- **The units spliced for the prescription `σ`** (the (CL) vine chains of `𝒱_0`, TARGET L1953-L1955).  B1a: with
the marked vine set `Mk` (default `∅`), the units of a marked group are its runs. -/
noncomputable def unitBlocks (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G) := ∅) :
    List (CLBlock G) :=
  (sgGroups G σ).flatMap (groupUnitsMk G Mk)

/-- B1a: membership in `unitBlocks` for every marked set. -/
theorem mem_unitBlocksMk {G : Garden w} {σ : Prescription G} {Mk : Set (Stage1.CLVine G)} {u : CLBlock G} :
    u ∈ unitBlocks G σ Mk ↔ ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      u ∈ groupUnitsMk G Mk S := by
  simp only [unitBlocks, List.mem_flatMap, mem_sgGroups]
  constructor
  · rintro ⟨S, ⟨h1, h2⟩, h3⟩; exact ⟨S, h1, h2, h3⟩
  · rintro ⟨S, h1, h2, h3⟩; exact ⟨S, ⟨h1, h2⟩, h3⟩

theorem mem_unitBlocks {G : Garden w} {σ : Prescription G} {u : CLBlock G} :
    u ∈ unitBlocks G σ ↔ ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      u ∈ (groupUnitsOf G S).units := by
  simp only [mem_unitBlocksMk, groupUnitsMk_empty]

/-- B1a: the units are pairwise disjoint for every marked set. -/
theorem unitBlocks_pairwiseMk {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (Mk : Set (Stage1.CLVine G)) :
    (unitBlocks G σ Mk).Pairwise (fun u u' => Disjoint u.atoms u'.atoms) := by
  classical
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
    have := (stage1Collection_isPartition hM).2.1
    rwa [hpart] at this
  unfold unitBlocks
  rw [List.pairwise_flatMap]
  refine ⟨fun S _ => groupUnitsMk_disj G Mk S, ?_⟩
  have hnd : (sgGroups G σ).Nodup := (Finset.nodup_toList _).filter _
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro S T hS hT hne u hu u' hu'
  have hSm := (mem_sgGroups.mp hS).1
  have hTm := (mem_sgGroups.mp hT).1
  exact (hdisj hSm hTm hne).mono (groupUnitsMk_sub hu) (groupUnitsMk_sub hu')

theorem unitBlocks_pairwise {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G) :
    (unitBlocks G σ).Pairwise (fun u u' => Disjoint u.atoms u'.atoms) :=
  unitBlocks_pairwiseMk hM σ ∅

/-- B1a: every atom of a unit lies in an unmarked vine of `𝒱_0` contained in the unit (`vinesV0 G σ Mk = 𝒱₀♮`). -/
theorem unitBlocks_soundMk {G : Garden w} {σ : Prescription G} {Mk : Set (Stage1.CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) :
    ∀ v ∈ u.atoms, ∃ c ∈ vinesV0 G σ Mk, v ∈ c.atoms ∧ c.atoms ⊆ u.atoms := by
  obtain ⟨S, hSm, hσ, hu⟩ := mem_unitBlocksMk.mp hu
  obtain ⟨cs, hcs, hiff⟩ := groupUnitsMk_sound hu
  intro v hv
  obtain ⟨c, hc, hvc⟩ := (hiff v).mp hv
  obtain ⟨hcV, hcM, hcI⟩ := hcs c hc
  refine ⟨c, ⟨hcV, S, hSm, hcI, hσ, hcM⟩, hvc, ?_⟩
  intro z hz
  exact (hiff z).mpr ⟨c, hc, hz⟩

/-- The survivors `𝒞_E` (in the skeleton), group by group (copied by source from the B0 probe, lines 196–203). -/
noncomputable def survivorsMk (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G)) :
    List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact (sgGroups G σ).flatMap fun S =>
    if markedGroup G Mk S then (if h : Nonempty (MarkedGroupUnits G S Mk) then (Classical.choice h).surv else [])
    else []

theorem survivorsMk_empty (G : Garden w) (σ : Prescription G) : survivorsMk G σ ∅ = [] := by
  simp [survivorsMk, markedGroup]

end WaveTurbulence.RedSplice
