/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkipMK
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull
public import WaveTurbulence.Foundations.Flower.MkMark.StemZero
public import WaveTurbulence.Foundations.Flower.MkMark.Batch
public import WaveTurbulence.Foundations.Flower.MkMark.BatchSel
public import WaveTurbulence.Foundations.Flower.MkMark.CountBound
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 9): further marked Stage-1′ declarations over `𝒱_γ`

The item-I declarations of L8's sub-areas (I-BASE, I-GATE) that became portable after waves 1–8 and the latest
publications, copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
  (hnm : ¬ Fama.markedGroup γF G Mk S)
include hM hSm hσ hsk hnm

/-- The unit with atoms `L0`. -/
theorem unit_LMkLow (hL : sk.L0 ≠ ∅) : ∃ u ∈ Fama.unitBlocks γF G σ Mk, u.atoms = sk.L0 := by
  obtain ⟨u, hu, hu'⟩ := (((Fama.groupUnitsOf γF G S).skip_units sk hsk).2.1).resolve_left hL
  exact ⟨u, Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu'⟩

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
  (hnm : ¬ Fama.markedGroup γF G Mk S)
include hM hSm hσ hsk hnm

theorem unit_RMkLow (hR : sk.R0 ≠ ∅) : ∃ u ∈ Fama.unitBlocks γF G σ Mk, u.atoms = sk.R0 := by
  obtain ⟨u, hu, hu'⟩ := (((Fama.groupUnitsOf γF G S).skip_units sk hsk).2.2).resolve_left hR
  exact ⟨u, Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu'⟩

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
  (hnm : ¬ Fama.markedGroup γF G Mk S)
include hM hSm hσ hsk hnm

/-- The unit of the left run, with its joints. -/
theorem unit_LMk'Low (hL : sk.L0 ≠ ∅) : ∃ u ∈ Fama.unitBlocks γF G σ Mk, u.atoms = sk.L0 ∧
    (u.upper = sk.a ∧ u.lower = sk.x ∨ u.upper = sk.x ∧ u.lower = sk.a) := by
  obtain ⟨u, hu, hu'⟩ := (((Fama.groupUnitsOf γF G S).skip_units sk hsk).2.1).resolve_left hL
  refine ⟨u, Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu', ?_⟩
  rcases ((Fama.groupUnitsOf γF G S).skip_units sk hsk).1 u hu with ⟨_, h⟩ | ⟨h1, _⟩
  · exact h
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨hu' ▸ hv, h1 ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hL
    rw [← hu']
    exact Finset.subset_empty.mp this

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
  (hnm : ¬ Fama.markedGroup γF G Mk S)
include hM hSm hσ hsk hnm

theorem unit_RMk'Low (hR : sk.R0 ≠ ∅) : ∃ u ∈ Fama.unitBlocks γF G σ Mk, u.atoms = sk.R0 ∧
    (u.upper = sk.y ∧ u.lower = sk.b ∨ u.upper = sk.b ∧ u.lower = sk.y) := by
  obtain ⟨u, hu, hu'⟩ := (((Fama.groupUnitsOf γF G S).skip_units sk hsk).2.2).resolve_left hR
  refine ⟨u, Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu', ?_⟩
  rcases ((Fama.groupUnitsOf γF G S).skip_units sk hsk).1 u hu with ⟨h1, _⟩ | ⟨_, h⟩
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨h1 ▸ hv, hu' ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hR
    rw [← hu']
    exact Finset.subset_empty.mp this
  · exact h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RedSplice
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- The (CL) block of a (CL) vine. -/
def clBlockOfLow {S : Garden w} (c : Fama.CLVineG γF S) : CLBlock S where
  atoms := c.atoms
  upper := c.upper
  lower := c.lower
  isBlock := (Src.isBlock_of_isSomeVine c.isVine)
  cl := ⟨c.notParentUpper, c.parentLower⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)

/-- The twist site of a family member that is a vine of `𝒱`. -/
def siteOfLow {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (c : Fama.CLVineG γF A.skeleton) (hc : c ∈ Fama.vinesVG γF A.skeleton)
    (he : c.atoms = A.family.atoms i) : Fama.TwistGroupSite γF A.skeleton where
  P := A.family.placement i
  S0 := A.family.atoms i
  a0 := A.family.upper i
  hB := (A.family.core i).1.1
  hCL := (A.family.core i).2.1
  hP := A.family.designated i
  Sg := hc.choose
  hSg := hc.choose_spec.1
  hS0 := he ▸ hc.choose_spec.2.1

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- Main's `Fama.VineA.NormalizedSplice.hinge_unit` for an unmarked group. -/
theorem hinge_unitMkLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hnm : ¬ Fama.markedGroup γF G Mk S)
    {a : GBranch G.tree} (ha : Fama.VineA.NormalizedSplice.groupJoint γF G S = some a)
    (hh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges) :
    σ S = Molecule.GapKind.SG ∧ ∃ u ∈ (Fama.groupUnitsOf γF G S).units, a ∈ u.atoms := by
  have haS := (Fama.VineA.NormalizedSplice.groupJoint_kind ha).1
  have h1 := ((Fama.stSt γF G σ Mk).mem_hinges _).mp hh
  rw [(Fama.stSt γF G σ Mk).M.ob_pi] at h1
  by_cases h : ∃ u ∈ Fama.unitBlocks γF G σ Mk, a ∈ u.atoms
  · obtain ⟨u, hu, hau⟩ := h
    obtain ⟨S'', hS''m, hσ, hmem⟩ := (Fama.mem_unitBlocksMk (Mk := Mk)).mp hu
    have hsub := Fama.groupUnitsMk_sub hmem hau
    by_cases hSS : S = S''
    · subst hSS
      rw [Fama.groupUnitsMk_of_not_marked hnm] at hmem
      exact ⟨hσ, u, hmem, hau⟩
    · exact absurd haS (fun h => Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS''m hSS) h hsub)
  · push Not at h
    have : repC (Fama.stSt γF G σ Mk).cls a = a := Fama.stSt_repC_noneMk hM σ h
    rw [this, Fama.stSt_cls_noneMk hM σ Mk h] at h1
    exact absurd rfl h1

end

end WaveTurbulence.GammaLow.Flower
