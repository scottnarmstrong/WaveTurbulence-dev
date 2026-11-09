/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineUnitTransport` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.Vine.A.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
/-! VINE-A2: actual splice units are good atom sets for a selected unit twist.
Their molecular block and CL orientation transport with the source atom map. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

private theorem disjoint_members (l : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    {u v : CLBlock G} (hu : u ∈ l) (hv : v ∈ l) (hne : u ≠ v) : Disjoint u.atoms v.atoms := by
  induction l generalizing u v with
  | nil => simp only [List.not_mem_nil] at hu
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hl
    rcases List.mem_cons.mp hu with rfl | hut
    · exact ha v ((List.mem_cons.mp hv).resolve_left (Ne.symm hne))
    · rcases List.mem_cons.mp hv with rfl | hvt
      · exact (ha u hut).symm
      · exact ih ht hut hvt hne

/-- Pairwise disjoint units that share an atom are the same unit. -/
theorem units_eq_of_mem_inter (l : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    {u v : CLBlock G} (hu : u ∈ l) (hv : v ∈ l)
    {z : GBranch G.tree} (hz : z ∈ u.atoms) (hz' : z ∈ v.atoms) : u = v := by
  by_contra hne
  exact (disjoint_left.mp (disjoint_members l hl hu hv hne) hz) hz'

/-- The CL orientation fixes both ordered Fama.joints of a block with a given atom set. -/
theorem clBlock_eq_of_atoms {u v : CLBlock G} (h : u.atoms = v.atoms) : u = v := by
  have hj := Vine.block_joints_unique G.molecule (h ▸ u.isBlock) v.isBlock
  have hu : u.upper = v.upper := by
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ha
    · exact (u.cl.1 (by rw [h, ha]; exact v.cl.2)).elim
  have hv : u.lower = v.lower := by
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨_, hb⟩ | ⟨ha, hb⟩
    · exact hb
    · exact (u.isBlock.2.2.2.1 (hu.trans hb.symm)).elim
  cases u
  cases v
  cases h
  cases hu
  cases hv
  rfl

/-- `vinesV0` membership via a covering unit, with the set difference (main `VineA.vinesV0_iff_unit_cover_diffMk`,
Vine/A/VineUnitCover.lean, from L5a's `Fama.VineA.vinesV0_iff_unit_coverMk`). -/
theorem vinesV0_iff_unit_cover_diffMkG {w : ℕ} (G : Garden w) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    (c : CLVineG γ G) :
    c ∈ Fama.vinesV0 γ G σ Mk ↔ c ∈ vinesVG γ G \ Mk ∧ ∃ u ∈ Fama.unitBlocks γ G σ Mk, c.atoms ⊆ u.atoms :=
  ⟨fun h => let ⟨a, b, d⟩ := (WaveTurbulence.GammaLow.Fama.VineA.vinesV0_iff_unit_coverMk G σ c).mp h; ⟨⟨a, b⟩, d⟩,
    fun ⟨⟨a, b⟩, d⟩ => (WaveTurbulence.GammaLow.Fama.VineA.vinesV0_iff_unit_coverMk G σ c).mpr ⟨a, b, d⟩⟩

/-- B1b (Mk-general form of `unitBlocks_good`). -/
theorem unitBlocks_goodMk (Z : Fama.TwistGroupSite γ G) (σ : Prescription G)
    {Mk : Set (CLVineG γ _)} (hsel : ∃ c ∈ Fama.vinesV0 γ (Mk := Mk) G σ, c.atoms = Z.S0) {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ (Mk := Mk) G σ) :
    Z.Good u.atoms := by
  obtain ⟨c, hc, hat⟩ := hsel
  obtain ⟨_, v, hv, hcv⟩ := (vinesV0_iff_unit_cover_diffMkG (Mk := Mk) G σ c).mp hc
  by_cases huv : u = v
  · subst v
    exact Or.inl (hat ▸ hcv)
  · right
    intro x hx hxu
    exact ((disjoint_left.mp (disjoint_members (Fama.unitBlocks γ (Mk := Mk) G σ)
      (Fama.unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu hv huv) hxu)
      (hcv (hat.symm ▸ hx))).elim

/-- Every actual unit either contains the active selected vine, or is disjoint from it. -/
theorem unitBlocks_good (Z : Fama.TwistGroupSite γ G) (σ : Prescription G)
    (hsel : ∃ c ∈ Fama.vinesV0 γ G σ, c.atoms = Z.S0) {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ) :
    Z.Good u.atoms := unitBlocks_goodMk (Mk := ∅) Z σ hsel hu

/-- The transported actual unit, with its CL property derived from source geometry. -/
noncomputable def unitImage (γ : ℝ) [Fact (γ ≤ 1 / 2)] (Z : Fama.TwistGroupSite γ G) (u : CLBlock G) (hgood : Z.Good u.atoms) :
    CLBlock Z.target where
  atoms := Z.iso.img u.atoms
  upper := Z.iso.e u.upper
  lower := Z.iso.e u.lower
  isBlock := Z.iso.isBlock_img u.isBlock
  cl := ⟨fun h => u.cl.1 ((Z.ip_map hgood u.isBlock.2.1).mp h),
    (Z.ip_map hgood u.isBlock.2.2.1).mpr u.cl.2⟩

/-- Distinct actual source units remain distinct actual CL blocks after transport. -/
theorem unitImage_injective (Z : Fama.TwistGroupSite γ G) {u v : CLBlock G}
    (hu : Z.Good u.atoms) (hv : Z.Good v.atoms) (h : unitImage γ Z u hu = unitImage γ Z v hv) : u = v :=
  clBlock_eq_of_atoms (Z.iso.img_injective (congrArg CLBlock.atoms h))

end WaveTurbulence.GammaLow.Famc.VineA
