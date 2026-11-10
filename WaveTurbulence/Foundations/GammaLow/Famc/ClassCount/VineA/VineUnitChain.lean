/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineUnitChain` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.Vine.A.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
/-! Actual splice units are vine chains, with their declared CL orientation.
This includes runs of HVC adjoints, transported back to the original molecule. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- The two declared skipped runs are chains of the original garden molecule. -/
theorem skip_runs_chain {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S) :
    (sk.L0 = ∅ ∨ ∃ n, Src.Chain γ G.molecule sk.L0 sk.a sk.x n) ∧
    (sk.R0 = ∅ ∨ ∃ n, Src.Chain γ G.molecule sk.R0 sk.y sk.b n) := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    exact cut_runs_chain (sk.skelM hb) hi
  | some e =>
    obtain ⟨n, _, hi⟩ := sk.chainN e hb
    have H := sk.skelN e hb
    have hc := cut_runs_chain H hi
    have he := (sk.blockN e hb).1
    constructor
    · rcases hc.1 with h | ⟨m, hm⟩
      · exact Or.inl h
      · right
        have hmiss : ¬ (sk.a ∈ sk.L0 ∧ sk.b ∈ sk.L0) :=
          fun h => cut_left_misses_end H h.2
        exact ⟨m, (eraseBond_local_embedding G.molecule e sk.L0
          (not_inGroup_of_ends G.molecule he hmiss))|> fun F => Fama.LocalDart.chain_to F hm (subset_refl _)⟩
    · rcases hc.2 with h | ⟨m, hm⟩
      · exact Or.inl h
      · right
        have hmiss : ¬ (sk.a ∈ sk.R0 ∧ sk.b ∈ sk.R0) :=
          fun h => cut_right_misses_start H h.1
        exact ⟨m, (eraseBond_local_embedding G.molecule e sk.R0
          (not_inGroup_of_ends G.molecule he hmiss))|> fun F => Fama.LocalDart.chain_to F hm (subset_refl _)⟩

/-- Src.Chain γ existence respects the uniquely determined unordered block Fama.joints. -/
theorem chain_rejoint_exists {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b x y : V}
    (hB : M.IsBlock S a b) (hC : ∃ n, Src.Chain γ M S a b n) (hB' : M.IsBlock S x y) :
    ∃ n, Src.Chain γ M S x y n := by
  have hj := block_joints_unique M hB hB'
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hC
  · obtain ⟨n, hn⟩ := hC
    obtain ⟨L, hL⟩ := Fama.Spine.of_chain hn
    exact ⟨_, hL.reverse.chain⟩

/-- Every actual group unit has an actual Fama.chain in the CL joint order. -/
theorem groupUnit_chain {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    {u : CLBlock G} (hu : u ∈ U.units) :
    ∃ n, Src.Chain γ G.molecule u.atoms u.upper u.lower n := by
  cases hs : U.skip with
  | none =>
    have hnon : U.units ≠ [] := fun he => by
      rw [he] at hu
      exact List.not_mem_nil hu
    obtain ⟨a, b, hB, n, hn⟩ := U.whole_vc hs hnon
    have hat := U.noskip_units hs u hu
    apply chain_rejoint_exists (hat ▸ hB) ⟨n, hat ▸ hn⟩ u.isBlock
  | some sk =>
    have hc := skip_runs_chain sk
    rcases (U.skip_units sk hs).1 u hu with ⟨hat, hj⟩ | ⟨hat, hj⟩
    · have hne : sk.L0 ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm
        exact Finset.notMem_empty u.upper hm
      obtain ⟨n, hn⟩ := hc.1.resolve_left hne
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨n, by rw [hat, hup, hlo]; exact hn⟩
      · obtain ⟨L, hL⟩ := Fama.Spine.of_chain hn
        exact ⟨_, by rw [hat, hup, hlo]; exact hL.reverse.chain⟩
    · have hne : sk.R0 ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm
        exact Finset.notMem_empty u.upper hm
      obtain ⟨n, hn⟩ := hc.2.resolve_left hne
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨n, by rw [hat, hup, hlo]; exact hn⟩
      · obtain ⟨L, hL⟩ := Fama.Spine.of_chain hn
        exact ⟨_, by rw [hat, hup, hlo]; exact hL.reverse.chain⟩

/-- B1a: every unit of a group (main's units of an unmarked group, the runs of a marked one) is a Fama.chain. -/
theorem groupUnitsMk_chain {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)} {u : CLBlock G}
    (hu : u ∈ Fama.groupUnitsMk γ G Mk S) : ∃ n, Src.Chain γ G.molecule u.atoms u.upper u.lower n := by
  classical
  unfold Fama.groupUnitsMk at hu
  split_ifs at hu with h1 h2
  · exact (Classical.choice h2).chain u hu
  · simp at hu
  · exact groupUnit_chain (Fama.groupUnitsOf γ G S) hu

/-- B1a: canonical unit-Fama.chain existence for every marked vine set. -/
theorem unitBlocks_chainMk {σ : Prescription G} {Mk : Set (CLVineG γ G)} {u : CLBlock G}
    (hu : u ∈ Fama.unitBlocks γ G σ Mk) : ∃ n, Src.Chain γ G.molecule u.atoms u.upper u.lower n := by
  obtain ⟨S, _, _, hm⟩ := Fama.mem_unitBlocksMk.mp hu
  exact groupUnitsMk_chain hm

end WaveTurbulence.GammaLow.Famc.VineA
