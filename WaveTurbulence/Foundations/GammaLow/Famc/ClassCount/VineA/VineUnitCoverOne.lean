/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineUnitCoverOne` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.Vine.A.VineUnitCoverOne
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
/-! Coverage by disjoint units respects the overlapping ingredients of a
spine. A skipped ingredient cannot itself belong to the selected carrier. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- An ingredient spine covered by pairwise disjoint units lies in a single unit. -/
theorem spine_cover_one_unit {D : Type} [Fintype D] [DecidableEq D]
    {N : Molecule (GBranch G.tree) D} {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (us : List (CLBlock G)) (hd : us.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hs : Fama.Spine γ N L S a b)
    (hc : ∀ t ∈ L, ∃ u ∈ us, t.1 ⊆ u.atoms) : ∃ u ∈ us, S ⊆ u.atoms := by
  induction hs with
  | @one T a b hv => exact hc (T, a, b) (List.mem_singleton_self _)
  | @snoc L U T a b c hs hv hi hne ih =>
    obtain ⟨u, hu, hU⟩ := ih (fun t ht => hc t (List.mem_append_left _ ht))
    obtain ⟨v, hvm, hT⟩ := hc (T, b, c) (List.mem_append_right _ (List.mem_singleton_self _))
    have he : u = v := units_eq_of_mem_inter us hd hu hvm
      (hU hs.ends.2.1) (hT (Fama.isSomeVine_ends hv).1)
    subst v
    exact ⟨u, hu, union_subset hU hT⟩

/-- Cover and the singleton run intersections exclude the skipped vine from V. -/
theorem skipped_not_vinesV {S : Finset (GBranch G.tree)}
    (U : Fama.GroupUnits γ G S) (hS : S ∈ maximalGroupsG γ G.molecule)
    (sk : Fama.SkipData γ G S) (hsk : U.skip = some sk)
    {c : CLVineG γ G} (hc : c ∈ vinesVG γ G) : c.atoms ≠ sk.A := by
  intro hat
  have hi : IsIngredientG γ G.molecule S c.atoms := hat.symm ▸ sk.ingredient
  obtain ⟨u, hu, hsub⟩ := U.cover (Mole.garden_isMolecule G) hS c hc hi
  have hxy := Fama.isSomeVine_ends sk.vine
  have hx : sk.x ∈ u.atoms := hsub (hat.symm ▸ hxy.1)
  have hy : sk.y ∈ u.atoms := hsub (hat.symm ▸ hxy.2.1)
  rcases (U.skip_units sk hsk).1 u hu with ⟨ha, _⟩ | ⟨ha, _⟩
  · rw [ha] at hx hy
    rcases sk.left with ⟨he, _⟩ | ⟨_, _, _, he⟩
    · rw [he] at hx; exact Finset.notMem_empty sk.x hx
    · have hz := mem_inter.mpr ⟨hy, hxy.2.1⟩
      rw [he, mem_singleton] at hz
      exact hxy.2.2 hz.symm
  · rw [ha] at hx hy
    rcases sk.right with ⟨he, _⟩ | ⟨_, _, _, he⟩
    · rw [he] at hy; exact Finset.notMem_empty sk.y hy
    · have hz := mem_inter.mpr ⟨hx, hxy.1⟩
      rw [he, mem_singleton] at hz
      exact hxy.2.2 hz

end WaveTurbulence.GammaLow.Famc.VineA
