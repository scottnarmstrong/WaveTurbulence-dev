/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceSkip` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRes4
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkip


/-!
# REDSPLICE-DEF (S2a): the skipped vine of an SG group inside the spliced skeleton

For an SG group `S` with a skipped ingredient (`SkipData`), the merge labelling `cls` of the global splice
satisfies the hypotheses of `SDecomp`: the two runs are collapsed to their crowns and nothing else of `S` is
merged.  Consequently the skipped vine is induced-isomorphic to its residual image in `𝒢_sb`
(`skipIso`, `skipIsoErase`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

/-- B1b (Mk-general form of `units_eq_of_not_disjoint`). -/
theorem units_eq_of_not_disjointMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {u u' : CLBlock G}
    {Mk : Set (CLVineG γ _)} (hu : u ∈ unitBlocks γ (Mk := Mk) G σ) (hu' : u' ∈ unitBlocks γ (Mk := Mk) G σ) (h : ¬ Disjoint u.atoms u'.atoms) : u = u' := by
  by_contra hne
  haveI : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
  exact h ((unitBlocks_pairwiseMk (Mk := Mk) hM σ).forall hu hu' hne)

/-- Distinct units are disjoint. -/
theorem units_eq_of_not_disjoint (hM : G.molecule.IsMolecule) (σ : Prescription G) {u u' : CLBlock G}
    (hu : u ∈ unitBlocks γ G σ) (hu' : u' ∈ unitBlocks γ G σ) (h : ¬ Disjoint u.atoms u'.atoms) : u = u' := units_eq_of_not_disjointMk (Mk := ∅) hM σ hu hu' h

section skip
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : SkipData γ G S} (hsk : (groupUnitsOf γ G S).skip = some sk)
include hM hSm hσ hsk

/-- No unit meets `S` outside the two runs. -/
theorem no_unit_outside {v : GBranch G.tree} (hvS : v ∈ S) (hL : v ∉ sk.L0) (hR : v ∉ sk.R0) :
    ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocks.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rcases ((groupUnitsOf γ G S').skip_units sk hsk).1 u hu' with ⟨h, _⟩ | ⟨h, _⟩
    · exact hL (h ▸ hv)
    · exact hR (h ▸ hv)
  · have hpart := partition_eq_maximalGroups (maximalGroupsG_partition (γ := γ) hM)
    have hdisj : (maximalGroupsG γ G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (maximalGroupsG_partition (γ := γ) hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) ((groupUnitsOf γ G S').sub u hu' hv) hvS

/-- The unit with atoms `L0`. -/
theorem unit_L (hL : sk.L0 ≠ ∅) : ∃ u ∈ unitBlocks γ G σ, u.atoms = sk.L0 := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf γ G S).skip_units sk hsk).2.1).resolve_left hL
  exact ⟨u, mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩, hu'⟩

theorem unit_R (hR : sk.R0 ≠ ∅) : ∃ u ∈ unitBlocks γ G σ, u.atoms = sk.R0 := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf γ G S).skip_units sk hsk).2.2).resolve_left hR
  exact ⟨u, mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩, hu'⟩

/-- The unit of the left run, with its joints. -/
theorem unit_L' (hL : sk.L0 ≠ ∅) : ∃ u ∈ unitBlocks γ G σ, u.atoms = sk.L0 ∧
    (u.upper = sk.a ∧ u.lower = sk.x ∨ u.upper = sk.x ∧ u.lower = sk.a) := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf γ G S).skip_units sk hsk).2.1).resolve_left hL
  refine ⟨u, mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩, hu', ?_⟩
  rcases ((groupUnitsOf γ G S).skip_units sk hsk).1 u hu with ⟨_, h⟩ | ⟨h1, _⟩
  · exact h
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨hu' ▸ hv, h1 ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hL
    rw [← hu']
    exact Finset.subset_empty.mp this

theorem unit_R' (hR : sk.R0 ≠ ∅) : ∃ u ∈ unitBlocks γ G σ, u.atoms = sk.R0 ∧
    (u.upper = sk.y ∧ u.lower = sk.b ∨ u.upper = sk.b ∧ u.lower = sk.y) := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf γ G S).skip_units sk hsk).2.2).resolve_left hR
  refine ⟨u, mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩, hu', ?_⟩
  rcases ((groupUnitsOf γ G S).skip_units sk hsk).1 u hu with ⟨h1, _⟩ | ⟨_, h⟩
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨h1 ▸ hv, hu' ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hR
    rw [← hu']
    exact Finset.subset_empty.mp this
  · exact h

/-- B1b (Mk-general form of `class_in_unit`). -/
theorem class_in_unitMk {u : CLBlock G} {Mk : Set (CLVineG γ _)} (hu : u ∈ unitBlocks γ (Mk := Mk) G σ) {v p : GBranch G.tree} (hv : v ∈ u.atoms)
    (h : repC (stSt γ (Mk := Mk) G σ).cls p = repC (stSt γ (Mk := Mk) G σ).cls v) : p ∈ u.atoms := by
  have hv' : repC (stSt γ (Mk := Mk) G σ).cls v = u.upper := stSt_repC_memMk (Mk := Mk) hM σ hu hv
  by_cases hp : ∃ u' ∈ unitBlocks γ (Mk := Mk) G σ, p ∈ u'.atoms
  · obtain ⟨u', hu', hpu'⟩ := hp
    have hp' : repC (stSt γ (Mk := Mk) G σ).cls p = u'.upper := stSt_repC_memMk (Mk := Mk) hM σ hu' hpu'
    have hup : u'.upper = u.upper := by rw [← hp', h, hv']
    have : u' = u := by
      apply units_eq_of_not_disjointMk (Mk := Mk) hM σ hu' hu
      rw [Finset.not_disjoint_iff]
      exact ⟨u.upper, hup ▸ u'.isBlock.2.1, u.isBlock.2.1⟩
    exact this ▸ hpu'
  · push Not at hp
    have hp' : repC (stSt γ (Mk := Mk) G σ).cls p = p := stSt_repC_noneMk (Mk := Mk) hM σ hp
    rw [hp', hv'] at h
    exact h ▸ u.isBlock.2.1

/-- The class of an atom of a unit lies in the unit. -/
theorem class_in_unit {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ) {v p : GBranch G.tree} (hv : v ∈ u.atoms)
    (h : repC (stSt γ G σ).cls p = repC (stSt γ G σ).cls v) : p ∈ u.atoms := class_in_unitMk (Mk := ∅) hM σ hSm hσ hsk hu hv h

/-- The skipped vine of an SG group satisfies the residual hypotheses for the global splice. -/
theorem skip_sdecomp {D' : Type} [Fintype D'] [DecidableEq D'] (N : Molecule (GBranch G.tree) D')
    (hskel : SkelDecomp N S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y) :
    SDecomp N (stSt γ G σ).cls S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y where
  toSkelDecomp := hskel
  hcls := (stSt γ G σ).hcls
  hLcl := by
    intro p v hv h
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_L hM σ hSm hσ hsk hL
    exact hua ▸ class_in_unit hM σ hSm hσ hsk hu (hua ▸ hv) h
  hRcl := by
    intro p v hv h
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_R hM σ hSm hσ hsk hR
    exact hua ▸ class_in_unit hM σ hSm hσ hsk hu (hua ▸ hv) h
  hLc := by
    intro p hp q hq
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_L hM σ hSm hσ hsk hL
    exact ⟨u.upper, stSt_cls_mem hM σ hu (hua ▸ hp), stSt_cls_mem hM σ hu (hua ▸ hq)⟩
  hRc := by
    intro p hp q hq
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_R hM σ hSm hσ hsk hR
    exact ⟨u.upper, stSt_cls_mem hM σ hu (hua ▸ hp), stSt_cls_mem hM σ hu (hua ▸ hq)⟩
  hNone := fun v hvS hL hR => stSt_cls_none hM σ (no_unit_outside hM σ hSm hσ hsk hvS hL hR)

end skip

end WaveTurbulence.GammaLow.Fama
