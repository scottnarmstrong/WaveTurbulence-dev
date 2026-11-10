/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P16
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkipMK
public import WaveTurbulence.Foundations.FinalCount.SubproGap2
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Vine.A.VineObjMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContained2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I (wave 17): the B4 layer of the marked Stage 1′ over `𝒱_γ`

The declarations on the path of main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s` (B4) not yet ported: L8's own (Stage1MKGate, MkSubpro,
Geometry *MK, Vine.A *MK) and the Stage-1 helpers that L6's H port has only at `Src.γL` (`FinalCount.S1Exists`,
`S1Overlap`, `S1Vinechain`, `S1Erase`, `S1Split`, `SubproObjMap`, `SubproGap2`, `AsmVN13`, `RedSpliceGapKind`), here
at the family `P.γ`/`γF`; copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

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

/-- No unit meets `S` outside the two runs. -/
theorem no_unit_outsideMkLow {v : GBranch G.tree} (hvS : v ∈ S) (hL : v ∉ sk.L0) (hR : v ∉ sk.R0) :
    ∀ u ∈ Fama.unitBlocks γF G σ Mk, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := Fama.mem_unitBlocksMk.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [Fama.groupUnitsMk_of_not_marked hnm] at hu'
    rcases ((Fama.groupUnitsOf γF G S').skip_units sk hsk).1 u hu' with ⟨h, _⟩ | ⟨h, _⟩
    · exact hL (h ▸ hv)
    · exact hR (h ▸ hv)
  · have hpart := Fama.partition_eq_maximalGroups (Fama.maximalGroupsG_partition (γ := γF) hM)
    have hdisj : (Fama.maximalGroupsG γF G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (Fama.maximalGroupsG_partition (γ := γF) hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) (Fama.groupUnitsMk_sub hu' hv) hvS

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

/-- The skipped vine of an SG group satisfies the residual hypotheses for the global splice. -/
theorem skip_sdecompMkLow {D' : Type} [Fintype D'] [DecidableEq D'] (N : Molecule (GBranch G.tree) D')
    (hskel : SkelDecomp N S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y) :
    SDecomp N (Fama.stSt γF G σ Mk).cls S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y where
  toSkelDecomp := hskel
  hcls := (Fama.stSt γF G σ Mk).hcls
  hLcl := by
    intro p v hv h
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_LMkLow hM σ hSm hσ hsk hnm hL
    exact hua ▸ Fama.class_in_unitMk (Mk := Mk) hM σ hSm hσ hsk hu (hua ▸ hv) h
  hRcl := by
    intro p v hv h
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_RMkLow hM σ hSm hσ hsk hnm hR
    exact hua ▸ Fama.class_in_unitMk (Mk := Mk) hM σ hSm hσ hsk hu (hua ▸ hv) h
  hLc := by
    intro p hp q hq
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_LMkLow hM σ hSm hσ hsk hnm hL
    exact ⟨u.upper, Fama.stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hp), Fama.stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hq)⟩
  hRc := by
    intro p hp q hq
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_RMkLow hM σ hSm hσ hsk hnm hR
    exact ⟨u.upper, Fama.stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hp), Fama.stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hq)⟩
  hNone := fun v hvS hL hR => Fama.stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_outsideMkLow hM σ hSm hσ hsk hnm hvS hL hR)

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **The vine object of the skipped vine of an SG VC group**, in `G_sb`: `π''A` with joints `π x`, `π y`:
a (CN) vine, or a root (CL) vine (TARGET subpro(2), `blockchainprop`). -/
theorem vc_objectMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
    (hnm : ¬ Fama.markedGroup γF G Mk S) (hbond : sk.bond = none) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
      O.atoms = sk.A.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.x ∧ O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.y ∧
      ∃ h, O.shape = Src.VineLikeObject.vc h := by
  have H := skip_sdecompMkLow hM σ hSm hσ hsk hnm G.molecule (sk.skelM hbond)
  have hc := (Fama.stSt γF G σ Mk).hcls
  let I := H.inducedIso ((Fama.stSt γF G σ Mk).M.toMol hc)
  have hX := sk.vine
  have hv : Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule (sk.A.image ((Fama.stSt γF G σ Mk).M.pi hc))
      ((Fama.stSt γF G σ Mk).M.pi hc sk.x) ((Fama.stSt γF G σ Mk).M.pi hc sk.y) := Fama.isSomeVine_iso I hX
  -- the (CL) pattern of the runs
  have hupx : sk.L0 ≠ ∅ → ((Fama.stSt γF G σ Mk).cls sk.x).getD sk.x = sk.x ∧ ¬ Mole.InternalParent G sk.L0 sk.x ∨
      (((Fama.stSt γF G σ Mk).cls sk.x).getD sk.x = sk.a ∧ ¬ Mole.InternalParent G sk.L0 sk.a ∧ Mole.InternalParent G sk.L0 sk.x) := by
    intro hL
    obtain ⟨u, hu, hua, hj⟩ := unit_LMk'Low hM σ hSm hσ hsk hnm hL
    have hxL := H.xL hL
    have hrc : ((Fama.stSt γF G σ Mk).cls sk.x).getD sk.x = u.upper := Fama.stSt_repC_memMk (Mk := Mk) hM σ hu (hua ▸ hxL)
    have hcl := u.cl
    rw [hua] at hcl
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨hrc.trans h1, ?_, ?_⟩
      · have := hcl.1; rwa [h1] at this
      · have := hcl.2; rwa [h2] at this
    · left
      refine ⟨hrc.trans h1, ?_⟩
      have := hcl.1; rwa [h1] at this
  have hupy : sk.R0 ≠ ∅ → ((Fama.stSt γF G σ Mk).cls sk.y).getD sk.y = sk.y ∧ ¬ Mole.InternalParent G sk.R0 sk.y ∨
      (((Fama.stSt γF G σ Mk).cls sk.y).getD sk.y = sk.b ∧ ¬ Mole.InternalParent G sk.R0 sk.b ∧ Mole.InternalParent G sk.R0 sk.y) := by
    intro hR
    obtain ⟨u, hu, hua, hj⟩ := unit_RMk'Low hM σ hSm hσ hsk hnm hR
    have hyR := H.yR hR
    have hrc : ((Fama.stSt γF G σ Mk).cls sk.y).getD sk.y = u.upper := Fama.stSt_repC_memMk (Mk := Mk) hM σ hu (hua ▸ hyR)
    have hcl := u.cl
    rw [hua] at hcl
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨hrc.trans h1, ?_⟩
      have := hcl.1; rwa [h1] at this
    · right
      refine ⟨hrc.trans h1, ?_, ?_⟩
      · have := hcl.1; rwa [h1] at this
      · have := hcl.2; rwa [h2] at this
  have ipx := ip_x H (Fama.stSt γF G σ Mk).M hc hupx
  have ipy := ip_y H (Fama.stSt γF G σ Mk).M hc hupy
  refine ⟨Fama.objVC γF _ _ _ hv, ?_, rfl, rfl, rfl, _, rfl⟩
  refine ⟨hv, ?_⟩
  rcases sk.kind with hcn | ⟨hroot, c, hca, htop⟩
  · exact Or.inl ⟨fun h => hcn.1 (ipx.mp h), fun h => hcn.2 (ipy.mp h)⟩
  · have hroot := hroot hbond
    have hc' : c.atoms = sk.A := hca
    have hB1 : G.molecule.IsBlock c.atoms c.upper c.lower := (Src.isBlock_of_isSomeVine c.isVine)
    have hB2 : G.molecule.IsBlock c.atoms sk.x sk.y := hc' ▸ (Src.isBlock_of_isSomeVine hX)
    have hjoint := Vine.block_joints_unique G.molecule hB1 hB2
    -- degree bound
    have hdeg : (Fama.stSt γF G σ Mk).G.molecule.deg ((Fama.stSt γF G σ Mk).M.pi hc sk.x) +
        (Fama.stSt γF G σ Mk).G.molecule.deg ((Fama.stSt γF G σ Mk).M.pi hc sk.y) ≤ 6 := by
      obtain ⟨a', b', hvc', _, hd6⟩ := hroot
      have hj := Vine.block_joints_unique G.molecule hvc'.1 (sk.blockM hbond)
      have h1 := H.deg_x_le ((Fama.stSt γF G σ Mk).M.toMol hc)
      have h2 := H.deg_y_le ((Fama.stSt γF G σ Mk).M.toMol hc)
      rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1; subst e2; exact (add_le_add h1 h2).trans hd6
      · subst e1; subst e2; rw [Nat.add_comm] at hd6; exact (add_le_add h1 h2).trans hd6
    refine Or.inr ⟨?_, hdeg⟩
    have hnp : ¬ Mole.InternalParent G c.atoms c.upper := c.notParentUpper
    have hp : Mole.InternalParent G c.atoms c.lower := c.parentLower
    rw [hc'] at hnp hp
    rcases Mole.finset_pair_eq_pair_iff.mp hjoint with ⟨hu, hl⟩ | ⟨hu, hl⟩
    · rw [hu] at hnp; rw [hl] at hp
      exact Or.inl ⟨fun h => hnp (ipx.mp h), ipy.mpr hp⟩
    · rw [hu] at hnp; rw [hl] at hp
      exact Or.inr ⟨fun h => hnp (ipy.mp h), ipx.mpr hp⟩

end

section
open WaveTurbulence.Subpro
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem isVC_mapLow {B0 : Finset V} {a b : V} (h : Src.IsVC γF N B0 a b) (hB0 : B0 ⊆ B) :
    Src.IsVC γF N' (B0.image I.π) (I.π a) (I.π b) :=
  ⟨(I.restrict hB0).isBlock h.1, by obtain ⟨n, hn⟩ := h.2; exact ⟨n, (Fama.InducedIso.chain_map I) hn hB0⟩⟩

alias _root_.WaveTurbulence.RedSplice.InducedIso.isVC_mapLow := isVC_mapLow

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

/-- Transport of the shape of a vine-like object. -/
@[expose] noncomputable def mapShapeLow {A : Finset V} {a b : V} (sh : Src.VineLikeObject γF N A a b)
    (hA : A ⊆ B) : Src.VineLikeObject γF N' (A.image I.π) (I.π a) (I.π b) :=
  match sh with
  | .vc h => .vc (I.isVC_mapLow h hA)
  | .hyper R =>
    have he : N.InGroup B R.added :=
      (inGroup_of_ends R.ends_eq (hA R.adjoint.1.2.1) (hA R.adjoint.1.2.2.1))
    .hyper
      { added := (I.e ⟨R.added, he⟩).1
        ends_eq := by rw [I.ends_comm ⟨R.added, he⟩]; show Sym2.map I.π (N.ends R.added) = _; rw [R.ends_eq]; rfl
        adjoint := (I.eraseE R.added he).isVC_mapLow R.adjoint hA }

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapShapeLow := mapShapeLow

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

/-- Transport of a vine-like object contained in `B`. -/
@[expose] noncomputable def mapObjLow (O : Src.Object γF N) (hO : O.atoms ⊆ B) : Src.Object γF N' :=
  ⟨O.atoms.image I.π, I.π O.upper, I.π O.lower, I.mapShapeLow O.shape hO⟩

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapObjLow := mapObjLow

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem mapObj_atomsLow (O : Src.Object γF N) (hO : O.atoms ⊆ B) :
    (I.mapObjLow O hO).atoms = O.atoms.image I.π := rfl

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem containsDart_mapLow (O : Src.Object γF N) (hO : O.atoms ⊆ B) {x : D} (hx : N.InGroup B x) :
    (I.mapObjLow O hO).ContainsDart (I.e ⟨x, hx⟩).1 ↔ O.ContainsDart x := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc h => exact I.inGroup_map_iff hO hx
  | hyper R =>
    have he : N.InGroup B R.added := inGroup_of_ends R.ends_eq (hO R.adjoint.1.2.1) (hO R.adjoint.1.2.2.1)
    show ((I.e ⟨x, hx⟩).1 ≠ (I.e ⟨R.added, he⟩).1 ∧ (I.e ⟨x, hx⟩).1 ≠ N'.mate (I.e ⟨R.added, he⟩).1 ∧
      N'.InGroup (A.image I.π) (I.e ⟨x, hx⟩).1) ↔ (x ≠ R.added ∧ x ≠ N.mate R.added ∧ N.InGroup A x)
    rw [I.inGroup_map_iff hO hx]
    have h1 := I.e_eq_iff he ⟨x, hx⟩
    have h2 := I.e_mate_iff he ⟨x, hx⟩
    simp only [] at h1 h2
    constructor
    · rintro ⟨a1, a2, a3⟩
      exact ⟨fun h => a1 (h1.mpr h), fun h => a2 (h2.mpr h), a3⟩
    · rintro ⟨a1, a2, a3⟩
      exact ⟨fun h => a1 (h1.mp h), fun h => a2 (h2.mp h), a3⟩

alias _root_.WaveTurbulence.RedSplice.InducedIso.containsDart_mapLow := containsDart_mapLow

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem mapObj_upperLow (O : Src.Object γF N) (hO : O.atoms ⊆ B) :
    (I.mapObjLow O hO).upper = I.π O.upper := rfl

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- The fine transport at a clean point, from the batch form of Lemma 2⁺(a). -/
theorem _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.fineTransportedAt_of_markInvariantBatchVLow {mk : Fama.Stage1Mk.MarkFn γF w}
    {Clean : ∀ {LG : LayeredGarden w}, PrimeData LG → Prop} (hV : Fama.Stage1Mk.MarkInvariantBatchV γF mk Clean)
    (a : Fama.VineA.PrescribedPrimeGarden γF w) (hc : Clean a.prime) : a.FineTransportedAt γF mk :=
  fun h => hV h a.prime.prime (fun i => ⟨i.1, i.2.1.1, rfl, (Fama.mem_vinesV0.mp i.2.1).2⟩) hc

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- **`FineMarking.fine` for `markIXLow (γF := γF)`**: every fine′ batch from every prescribed point carries `markIXLow (γF := γF)`. -/
theorem fineTransportedAt_markIXLow (a : Fama.VineA.PrescribedPrimeGarden γF w) : a.FineTransportedAt γF (markIXLow (γF := γF) J pat t s kSel) :=
  Fama.VineA.PrescribedPrimeGarden.fineTransportedAt_of_markInvariantBatchVLow (Clean := fun _ => True)
    (stage1Mk_markInvariantBatchV_markIXLow J pat t s kSel) a trivial

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- No unit meets an HV group. -/
theorem no_unit_hvMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hhv : ∃ a b, Src.IsHV γF G.molecule S a b)
    (hnhvc : ¬ ∃ a b, Src.IsHVC γF G.molecule S a b) {Mk : Set (Fama.CLVineG γF G)}
    (hnm : ¬ Fama.markedGroup γF G Mk S)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ Fama.unitBlocks γF G σ Mk, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := Fama.mem_unitBlocksMk.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [Fama.groupUnitsMk_of_not_marked hnm, (Fama.groupUnitsOf γF G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := Fama.partition_eq_maximalGroups (Fama.maximalGroupsG_partition (γ := γF) hM)
    have hdisj : (Fama.maximalGroupsG γF G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (Fama.maximalGroupsG_partition (γ := γF) hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) (Fama.groupUnitsMk_sub hu' hv) hvS

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- The residual of an SG HV group (not touched by the splice): the canonical triple gives the object. -/
theorem hv_objectMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) {a b : GBranch G.tree} {e : GardenDart G}
    (hnhvc : ¬ ∃ a b, Src.IsHVC γF G.molecule S a b) {Mk : Set (Fama.CLVineG γF G)}
    (hnm : ¬ Fama.markedGroup γF G Mk S)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Src.IsSomeVine γF (Mole.eraseBond G.molecule e) S a b) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
      O.atoms = S.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∧ O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls b ∧
      ∃ R : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (Fama.stSt γF G σ Mk).M.od R.added = e := by
  have hab : a ≠ b := (Src.isBlock_of_isSomeVine hvine).2.2.2.1
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
  have hnone : ∀ {v : GBranch G.tree}, v ∈ S → ∀ u ∈ Fama.unitBlocks γF G σ Mk, v ∉ u.atoms :=
    fun hv => no_unit_hvMkLow hM σ hSm ⟨a, b, e, hends, hvine⟩ hnhvc hnm hv
  have hsk : SkelDecomp (Mole.eraseBond G.molecule e) S S ∅ ∅ a b a b :=
    ⟨hN, by simp, (Src.isBlock_of_isSomeVine hvine), (Src.isBlock_of_isSomeVine hvine), Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Finset.disjoint_empty_left _⟩
  have H : SDecomp (Mole.eraseBond G.molecule e) (Fama.stSt γF G σ Mk).cls S S ∅ ∅ a b a b :=
    { toSkelDecomp := hsk
      hcls := (Fama.stSt γF G σ Mk).hcls
      hLcl := fun p v hv => by simp at hv
      hRcl := fun p v hv => by simp at hv
      hLc := fun p hp => by simp at hp
      hRc := fun p hp => by simp at hp
      hNone := fun v hvS _ _ => Fama.stSt_cls_noneMk (Mk := Mk) hM σ (hnone hvS) }
  exact Fama.VineA.NormalizedSplice.hyper_objectMk (Mk := Mk) σ H hends hvine

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- The HV of the skipped vine of an SG HVC group. -/
theorem hvc_objectMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : Fama.SkipData γF G S} (hsk : (Fama.groupUnitsOf γF G S).skip = some sk) {Mk : Set (Fama.CLVineG γF G)}
    (hnm : ¬ Fama.markedGroup γF G Mk S) {e : GardenDart G} (hbond : sk.bond = some e) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
      O.atoms = sk.A.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.x ∧ O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.y ∧
      ∃ R : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (Fama.stSt γF G σ Mk).M.od R.added = e :=
  Fama.VineA.NormalizedSplice.hyper_objectMk (Mk := Mk) σ (skip_sdecompMkLow hM σ hSm hσ hsk hnm _ (sk.skelN e hbond)) (sk.blockN e hbond).1
    (sk.vineN e hbond)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

theorem exists_objMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : Fama.VineA.NormalizedSplice.HasObj γF G S)
    {Mk : Set (Fama.CLVineG γF G)} (hnm : ¬ Fama.markedGroup γF G Mk S) :
    ∃ O, Fama.VineA.NormalizedSplice.ObjSpecMk γF G σ S Mk O := by
  have hc := (Fama.stSt γF G σ Mk).hcls
  have hsk_or : (((∃ a b, Src.IsHV γF G.molecule S a b) ∧
      ¬ ∃ a b, Src.IsHVC γF G.molecule S a b) ∧ (Fama.groupUnitsOf γF G S).skip = none) ∨
      ∃ sk : Fama.SkipData γF G S, (Fama.groupUnitsOf γF G S).skip = some sk := by
    rcases h with hl | hr
    · rcases hs : (Fama.groupUnitsOf γF G S).skip with _ | sk
      · exact Or.inl ⟨hl, rfl⟩
      · exact Or.inr ⟨sk, rfl⟩
    · exact Or.inr hr
  rcases hsk_or with ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone⟩ | ⟨sk, hsk⟩
  · obtain ⟨a0, b0, e0, hpk, hends, hvine⟩ := Fama.VineA.hvGroupPick_some ⟨hSm, ⟨a, b, hhv⟩, hnhvc⟩
    obtain ⟨O, hO, hOa, hou, hol, R, hR, hRe⟩ := hv_objectMkLow hM σ hSm hnhvc hnm hends hvine
    refine ⟨O, hO, ?_, ?_, ⟨S, subset_refl _, hOa, fun z hz _ => hz,
      Or.inl ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone, a0, b0, e0, hpk, hou, hol, R, hR, hRe⟩⟩⟩
    · intro v hv
      rw [hOa] at hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨z, hz, rfl⟩
    · intro c hcn hcO
      exfalso
      rw [hOa] at hcO
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcO
      apply hcn
      rw [(Fama.stSt γF G σ Mk).M.ob_pi hc]
      have hnone := Fama.stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_hvMkLow hM σ hSm ⟨a, b, hhv⟩ hnhvc hnm hz)
      have hr : repC (Fama.stSt γF G σ Mk).cls z = z := by simp [repC, hnone]
      rw [hr]; exact hnone
  · rcases hb : sk.bond with _ | e
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := vc_objectMkLow hM σ hSm hσ hsk hnm hb
      have H := skip_sdecompMkLow hM σ hSm hσ hsk hnm G.molecule (sk.skelM hb)
      exact ⟨O, Fama.VineA.NormalizedSplice.objSpec_of_skipMk hM σ sk (Mk := Mk) O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => H.nonmerged_mem hz hn) hsk (fun _ => hsh)
        (fun e' he' => by rw [hb] at he'; cases he')⟩
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := hvc_objectMkLow hM σ hSm hσ hsk hnm hb
      have H := skip_sdecompMkLow hM σ hSm hσ hsk hnm (Mole.eraseBond G.molecule e) (sk.skelN e hb)
      exact ⟨O, Fama.VineA.NormalizedSplice.objSpec_of_skipMk hM σ sk (Mk := Mk) O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => H.nonmerged_mem hz hn) hsk (fun h => by rw [hb] at h; cases h)
        (fun e' he' => by
          rw [hb] at he'
          have : e = e' := Option.some.inj he'
          subst this
          exact hsh)⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **`𝒞₁` at `Mk`: an unmarked SG group with an object has its object in `Fama.VineA.NormalizedSplice.objects γF G σ Mk`.** -/
theorem objOf_isSomeMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : Fama.VineA.NormalizedSplice.HasObj γF G S)
    {Mk : Set (Fama.CLVineG γF G)} (hnm : ¬ Fama.markedGroup γF G Mk S) :
    ∃ O, Fama.VineA.NormalizedSplice.objOf γF G σ S Mk = some O ∧ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk := by
  classical
  have hex : G.molecule.IsMolecule ∧ S ∈ Fama.maximalGroupsG γF G.molecule ∧ σ S = Molecule.GapKind.SG ∧ Fama.VineA.NormalizedSplice.HasObj γF G S ∧
      ¬ Fama.markedGroup γF G Mk S ∧ ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, Fama.VineA.NormalizedSplice.ObjSpecMk γF G σ S Mk O :=
    ⟨hM, hSm, hσ, h, hnm, exists_objMkLow hM σ hSm hσ h hnm⟩
  have hO : Fama.VineA.NormalizedSplice.objOf γF G σ S Mk = some (Classical.choose hex.2.2.2.2.2) := by
    unfold Fama.VineA.NormalizedSplice.objOf
    rw [dite_eq_left hex]
  refine ⟨_, hO, ?_⟩
  unfold Fama.VineA.NormalizedSplice.objects
  exact List.mem_filterMap.mpr ⟨S, Fama.mem_sgGroups.mpr ⟨hSm, hσ⟩, hO⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- **o75 Theorem 7.5′(4) for the marked splice** (main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_atoms` with survivors): an object of `G_sb`
avoiding the hinges and the survivor joints, not inside an object of `𝒞₁` nor inside a survivor, lies in a DV or in
an LG/ZG object, disjoint from the hinges, from `𝒞₁` and from the survivors. -/
theorem contained_atomsMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (hMkSG : Mk ⊆ Fama.vinesV0 γF G σ) {d : ℕ}
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base z ≠ 0)
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule)
    (hout : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, ¬ P.atoms ⊆ O.atoms)
    (hsurv : ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), ¬ P.atoms ⊆ (survObjLow ht).atoms)
    (hdis : Disjoint P.atoms (Fama.stSt γF G σ Mk).hinges)
    (hJ : ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), (survObjLow ht).upper ∉ P.atoms ∧ (survObjLow ht).lower ∉ P.atoms) :
    (∃ S a b, Src.IsDV γF (Fama.stSt γF G σ Mk).G.molecule S a b ∧ P.atoms ⊆ S ∧ Disjoint S (Fama.stSt γF G σ Mk).hinges ∧
        (∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, Disjoint S O.atoms) ∧
        ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), Disjoint S (survObjLow ht).atoms) ∨
      ∃ Q : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z) Molecule.GapKind.LG ∨
          Q.HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z) Molecule.GapKind.ZG) ∧
        Disjoint Q.atoms (Fama.stSt γF G σ Mk).hinges ∧ (∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, Disjoint Q.atoms O.atoms) ∧
        ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), Disjoint Q.atoms (survObjLow ht).atoms := by
  classical
  have hB := Famc.Subpro.VineA.NormalizedSplice.Subpro.nohinge_unmergedMk σ hdis
  obtain ⟨I, hIπ, -⟩ := exists_iso_down (Fama.stSt γF G σ Mk).M (Fama.stSt γF G σ Mk).hcls P.atoms hB
  have hP0 : Fama.IsVineLikeSetG γF G.molecule (P.atoms.image (Fama.stSt γF G σ Mk).M.ob) := by
    have := Fama.isVineLikeSet_of_object (I.mapObjLow P (subset_refl _))
    rw [mapObj_atomsLow, hIπ] at this
    exact this
  obtain ⟨g, hg, hPg⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.cover_group hM hP0
  have hPg' : ∀ c ∈ P.atoms, (Fama.stSt γF G σ Mk).M.ob c ∈ g := fun c hc => hPg (Finset.mem_image_of_mem _ hc)
  have hne : P.upper ∈ P.atoms := Fama.VineA.NormalizedSplice.Object.upper_mem P
  -- (d): a marked group; `P` lies in one survivor
  by_cases hgm : Fama.markedGroup γF G Mk g
  · exfalso
    obtain ⟨t, ht, hsub⟩ := obj_in_survivorLow hM σ hg (sg_of_markedGroupLow hMkSG hg hgm) hgm P
      (fun p hp => ⟨_, hPg' p hp, (Famc.Subpro.VineA.NormalizedSplice.Subpro.pi_obMk σ (hB p hp)).symm⟩) hdis hJ
    exact hsurv t ht hsub
  have hgU : Fama.groupUnitsMk γF G Mk g = (Fama.groupUnitsOf γF G g).units := Fama.groupUnitsMk_of_not_marked hgm
  by_cases hmeet : ∃ u ∈ Fama.unitBlocks γF G σ Mk, ∃ z0 ∈ g, z0 ∈ u.atoms
  · exfalso
    obtain ⟨u, hu, z0, hz0g, hz0u⟩ := hmeet
    obtain ⟨S'', hS''m, hσ'', hu''⟩ := Fama.mem_unitBlocksMk.mp hu
    have hgS : S'' = g := by
      by_contra hne'
      exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS''m hg hne') (Fama.groupUnitsMk_sub hu'' hz0u) hz0g
    subst hgS
    have hu_g : u ∈ (Fama.groupUnitsOf γF G S'').units := hgU ▸ hu''
    rcases hskip : (Fama.groupUnitsOf γF G S'').skip with _ | sk
    · have hua := (Fama.groupUnitsOf γF G S'').noskip_units hskip u hu_g
      have hcl := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hPg' P.upper hne : (Fama.stSt γF G σ Mk).M.ob P.upper ∈ u.atoms)
      rw [hB _ hne] at hcl
      cases hcl
    · obtain ⟨O, hO, hOm⟩ := objOf_isSomeMkLow hM σ hg hσ'' (Or.inr ⟨sk, hskip⟩) hgm
      exact hout O hOm (Famc.Subpro.VineA.NormalizedSplice.Subpro.atoms_sub_objMk hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
  · have hall : ∀ z0 ∈ g, (Fama.stSt γF G σ Mk).cls z0 = none := fun z0 hz0 =>
      Fama.stSt_cls_noneMk (Mk := Mk) hM σ (fun u hu hzu => hmeet ⟨u, hu, z0, hz0, hzu⟩)
    by_cases hobj : σ g = Molecule.GapKind.SG ∧ Fama.VineA.NormalizedSplice.HasObj γF G g
    · exfalso
      obtain ⟨O, hO, hOm⟩ := objOf_isSomeMkLow hM σ hg hobj.1 hobj.2 hgm
      exact hout O hOm (Famc.Subpro.VineA.NormalizedSplice.Subpro.atoms_sub_objMk hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
    · have hO : Fama.VineA.NormalizedSplice.objOf γF G σ g Mk = none := Famc.Subpro.VineA.NormalizedSplice.Subpro.objOf_noneMk σ (fun h => hobj ⟨h.2.2.1, h.2.2.2⟩)
      have hdisH := Famc.Subpro.VineA.NormalizedSplice.Subpro.image_pi_disjoint_hingesMk σ hall
      have hdisO := Famc.Subpro.VineA.NormalizedSplice.Subpro.image_pi_disjoint_objectsMk hM σ hg hall hO
      have hdisS := fun t (ht : t ∈ Fama.survivorsMk γF G σ Mk) => image_disjoint_survObjLow hM σ hg hgm hall ht
      obtain ⟨I2, hI2π, hI2od⟩ := exists_iso_up (Fama.stSt γF G σ Mk).M (Fama.stSt γF G σ Mk).hcls g hall
      have hPsub : P.atoms ⊆ g.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) := by
        intro c hc
        exact Finset.mem_image.mpr ⟨(Fama.stSt γF G σ Mk).M.ob c, hPg' c hc, Famc.Subpro.VineA.NormalizedSplice.Subpro.pi_obMk σ (hB c hc)⟩
      by_cases hvl : Fama.IsVineLikeSetG γF G.molecule g
      · right
        obtain ⟨a, Q, ha, hQ, e, he, hek, hnh', -⟩ := gapSpecification_pair_of_objectMkLow hM σ hg hgm
        obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
        rw [ha] at ha'; cases ha'
        have haQ : a = Q.upper := hdes.1
        have haG : a ∈ g := (Fama.VineA.NormalizedSplice.groupJoint_kind ha).1
        have hQa : Q.atoms = g := by
          rcases hsk : (Fama.groupUnitsOf γF G g).skip with _ | sk
          · by_cases hu : (Fama.groupUnitsOf γF G g).units = []
            · exact hdes.2.2.2.2.2.2.1 hsk hu hvl
            · exact (hdes.2.2.2.2.1 hsk hu).1
          · rcases hb : sk.bond with _ | e'
            · exact (hdes.2.2.1 sk hsk hb).1
            · exact (hdes.2.2.2.1 sk e' hsk hb).1
        have hσne : σ g ≠ Molecule.GapKind.SG := by
          intro hσ
          apply hobj
          refine ⟨hσ, ?_⟩
          have hvl' : (∃ a b, Src.IsVC γF G.molecule g a b ∨ Src.IsHVC γF G.molecule g a b) → Fama.VineA.NormalizedSplice.HasObj γF G g := by
            intro hx
            rcases (Fama.groupUnitsOf γF G g).vl hM hg hx with hu | ⟨sk, hsk⟩
            · exfalso
              obtain ⟨u, hu'⟩ := List.exists_mem_of_ne_nil _ hu
              exact hmeet ⟨u, Fama.mem_unitBlocksMk.mpr ⟨g, hg, hσ, hgU ▸ hu'⟩, u.upper,
                (Fama.groupUnitsOf γF G g).sub u hu' u.isBlock.2.1, u.isBlock.2.1⟩
            · exact Or.inr ⟨sk, hsk⟩
          obtain ⟨a0, b0, hab⟩ := hvl
          rcases hab with hhv | hvc | hhvc
          · by_cases hh : ∃ a b, Src.IsHVC γF G.molecule g a b
            · exact hvl' (by obtain ⟨a', b', h'⟩ := hh; exact ⟨a', b', Or.inr h'⟩)
            · exact Or.inl ⟨⟨a0, b0, hhv⟩, hh⟩
          · exact hvl' ⟨a0, b0, Or.inl hvc⟩
          · exact hvl' ⟨a0, b0, Or.inr hhvc⟩
        have hnotH : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges := by
          intro hh
          have := ((Fama.stSt γF G σ Mk).mem_hinges _).mp hh
          rw [(Fama.stSt γF G σ Mk).M.ob_pi, repC_of_none (hall a haG)] at this
          exact this (hall a haG)
        obtain ⟨-, hc1, hc2⟩ := hnh' hnotH
        have hk := gapKind_of_Z (Fama.stSt γF G σ Mk).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
        rw [hek] at hk
        have hQsub : Q.atoms ⊆ g := hQa ▸ subset_refl _
        set Q' := I2.mapObjLow Q hQsub with hQ'
        have hQ'a : Q'.atoms = g.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) := by
          rw [hQ', mapObj_atomsLow, hQa, hI2π]
        have hcd : ∀ f : GardenDart (Fama.stSt γF G σ Mk).G, Q.ContainsDart ((Fama.stSt γF G σ Mk).M.od f) →
            Q'.ContainsDart f := by
          intro f hf
          have hx : G.molecule.InGroup g ((Fama.stSt γF G σ Mk).M.od f) := hQa ▸ Famc.Subpro.VineA.NormalizedSplice.Subpro.containsDart_inGroup Q hf
          have h1 := (I2.containsDart_mapLow Q hQsub hx).mpr hf
          have h2 : (I2.e ⟨(Fama.stSt γF G σ Mk).M.od f, hx⟩).1 = f := (Fama.stSt γF G σ Mk).M.od_inj (hI2od ⟨_, hx⟩)
          rw [h2] at h1
          exact h1
        have hQ'up : Q'.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls Q.upper := by
          rw [hQ', mapObj_upperLow, hI2π]
        have hgap : ∀ k, k = σ g → Q'.HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z) k := by
          intro k hk'
          exact Fama.hasGapKind_of_pair Q' L γ η base _ e.first e.second (e.at_first.trans (haQ ▸ hQ'up).symm)
            (e.at_second.trans (haQ ▸ hQ'up).symm) e.opposite (hcd _ hc1) (hcd _ hc2) k (hk.trans hk'.symm)
        refine ⟨Q', hQ'a ▸ hPsub, ?_, hQ'a ▸ hdisH, fun O hO' => hQ'a ▸ hdisO O hO',
          fun t ht => hQ'a ▸ hdisS t ht⟩
        cases hs : σ g
        · exact Or.inr (hgap _ hs.symm)
        · exact absurd hs hσne
        · exact Or.inl (hgap _ hs.symm)
      · left
        have hst := hg.1
        rcases Fama.isStage1Group_iff.mp hst with hv | ⟨a, b, hdv⟩
        · exact absurd hv hvl
        · have := I2.isDV_mapFc hdv (subset_refl _)
          rw [hI2π] at this
          exact ⟨g.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls), _, _, this, hPsub, hdisH, hdisO, hdisS⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.far_dart` at every marking. -/
theorem far_dartMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule) (jf : GBranch (Fama.stSt γF G σ Mk).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (Fama.stSt γF G σ Mk).hinges → jf c = (Fama.stSt γF G σ Mk).M.ob c)
    (hK : KDataMkLow σ P jf) {w : GBranch (Fama.stSt γF G σ Mk).G.tree} (hw : w ∈ P.atoms) (hwh : w ∈ (Fama.stSt γF G σ Mk).hinges)
    {d : GardenDart (Fama.stSt γF G σ Mk).G} (hd : (Fama.stSt γF G σ Mk).G.molecule.atom d = w) (hnc : ¬ P.ContainsDart d) :
    G.molecule.atom ((Fama.stSt γF G σ Mk).M.od d) ∉ P.atoms.image jf := by
  classical
  intro hmem
  obtain ⟨hwj, u, hu, hob, hjw, hKw⟩ := hK w hw hwh
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P hwj true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P hwj false
  obtain ⟨hdm, hde, hdj⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crown_dartMk hM σ hu hob hd
  have hatom : G.molecule.atom ((Fama.stSt γF G σ Mk).M.od d) = jf w := by
    obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hmem
    by_cases hch : c ∈ (Fama.stSt γF G σ Mk).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hK c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u := Fama.VineA.NormalizedSplice.unit_eq_of_memMk hM σ huc hu hjcm (hcj ▸ hdm)
      subst hucu
      have : c = w := (Fama.stSt γF G σ Mk).M.ob_inj (hobc.trans hob.symm)
      rw [← hcj, this]
    · exfalso
      have h1 : (Fama.stSt γF G σ Mk).cls (G.molecule.atom ((Fama.stSt γF G σ Mk).M.od d)) = some u.upper :=
        Fama.stSt_cls_memMk (Mk := Mk) hM σ hu hdm
      have h2 : (Fama.stSt γF G σ Mk).cls (jf c) = none := by
        rw [hjnon c hc hch]
        by_contra hne
        exact hch (((Fama.stSt γF G σ Mk).mem_hinges c).mpr hne)
      rw [← hcj, h2] at h1
      cases h1
  have hblock : ∃ j', G.molecule.IsBlock u.atoms (jf w) j' := by
    rcases hjw with h | h
    · exact ⟨u.lower, h ▸ u.isBlock⟩
    · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
  have hcard := joint_ext_card hM hblock.choose_spec
  set E := (G.molecule.dartsAt (jf w)).filter (fun e => ¬ G.molecule.InGroup u.atoms e) with hE
  have hao_a := hKw ao hao hao_c
  have hai_a := hKw ai hai hai_c
  have hoE : (Fama.stSt γF G σ Mk).M.od ao ∈ E := by
    obtain ⟨-, hext, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crown_dartMk hM σ hu hob hao
    simp [hE, Molecule.dartsAt, hao_a, hext]
  have hiE : (Fama.stSt γF G σ Mk).M.od ai ∈ E := by
    obtain ⟨-, hext, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crown_dartMk hM σ hu hob hai
    simp [hE, Molecule.dartsAt, hai_a, hext]
  have hne : (Fama.stSt γF G σ Mk).M.od ao ≠ (Fama.stSt γF G σ Mk).M.od ai := by
    intro h
    have := congrArg G.molecule.out h
    rw [(Fama.stSt γF G σ Mk).M.od_out, (Fama.stSt γF G σ Mk).M.od_out, hao_o, hai_o] at this
    cases this
  have hE2 : E = {(Fama.stSt γF G σ Mk).M.od ao, (Fama.stSt γF G σ Mk).M.od ai} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hoE
      · rw [Finset.mem_singleton.mp he]; exact hiE
    · have : ({(Fama.stSt γF G σ Mk).M.od ao, (Fama.stSt γF G σ Mk).M.od ai} : Finset (GardenDart G)).card = 2 :=
        Finset.card_pair hne
      omega
  have hdE : (Fama.stSt γF G σ Mk).M.od d ∈ E := by simp [hE, Molecule.dartsAt, hatom, hde]
  rw [hE2] at hdE
  rcases Finset.mem_insert.mp hdE with h | h
  · exact hnc (by rw [(Fama.stSt γF G σ Mk).M.od_inj h]; exact hao_c)
  · exact hnc (by rw [(Fama.stSt γF G σ Mk).M.od_inj (Finset.mem_singleton.mp h)]; exact hai_c)

end

end WaveTurbulence.GammaLow.Flower
