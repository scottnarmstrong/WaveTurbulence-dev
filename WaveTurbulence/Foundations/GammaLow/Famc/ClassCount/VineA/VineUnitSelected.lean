/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineUnitSelected` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.Vine.A.VineUnitSelected
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Every actual unit has a spine of V ingredients. For an SG group these
are exactly selected ingredients, so disjoint-unit coverage can be transported. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- The declared skipped runs have selected spines without a choice of adjoint. -/
theorem skip_runs_selected {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    (hS : S ∈ maximalGroupsG γ G.molecule) (sk : Fama.SkipData γ G S) (hsk : U.skip = some sk) :
    (sk.L0 = ∅ ∨ ∃ LL, Fama.Spine γ G.molecule LL sk.L0 sk.a sk.x ∧
      ∀ t ∈ LL, ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1) ∧
    (sk.R0 = ∅ ∨ ∃ RR, Fama.Spine γ G.molecule RR sk.R0 sk.y sk.b ∧
      ∀ t ∈ RR, ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1) := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    obtain ⟨L, hs, hA⟩ := Fama.Spine.mem_of_ingredient hi
    exact skipped_run_spines U hS sk hsk (sk.skelM hb) hs hA
      (fun T p q ht => (hs.mem_vine ht).1)
      (fun T p q ht => Or.inl ⟨sk.a, sk.b, L.length, p, q, sk.blockM hb, hs.ingredient_of_mem ht⟩)
  | some e =>
    obtain ⟨n, hn, hi⟩ := sk.chainN e hb
    have H := sk.skelN e hb
    obtain ⟨L, hs, hlen⟩ := Fama.Spine.of_chain_len (chainIngredientG_spec hi).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn
    have hA := hs.ingredient_mem H.mol H.hSB hi
    have he := (sk.blockN e hb).1
    exact skipped_run_spines U hS sk hsk H hs hA
      (fun T p q ht => (Fama.vine_transfer G.molecule he (hs.not_both hlen2 ht) p q).mp (hs.mem_vine ht).1)
      (fun T p q ht => Or.inr ⟨sk.a, sk.b, e, L.length, p, q, he, hlen2, H.hSB, hs.ingredient_of_mem ht⟩)

/-- A spine and its V-membership assertions can be read in the opposite direction. -/
theorem selected_spine_reverse {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Fama.Spine γ G.molecule L S a b)
    (hc : ∀ t ∈ L, ∃ c ∈ vinesVG γ G, c.atoms = t.1) :
    ∃ R, Fama.Spine γ G.molecule R S b a ∧ ∀ t ∈ R, ∃ c ∈ vinesVG γ G, c.atoms = t.1 := by
  refine ⟨_, hs.reverse, ?_⟩
  intro ⟨T, p, q⟩ ht
  exact hc (T, q, p) (Fama.mem_revSwap.mp ht)

/-- Every chosen group unit is an actual spine of selected source ingredients. -/
theorem groupUnit_selected_spine {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    (hS : S ∈ maximalGroupsG γ G.molecule) {u : CLBlock G} (hu : u ∈ U.units) :
    ∃ L, Fama.Spine γ G.molecule L u.atoms u.upper u.lower ∧
      ∀ t ∈ L, ∃ c ∈ vinesVG γ G, c.atoms = t.1 := by
  cases hsk : U.skip with
  | none =>
    obtain ⟨n, hn⟩ := groupUnit_chain U hu
    obtain ⟨L, hs⟩ := Fama.Spine.of_chain hn
    have hat := U.noskip_units hsk u hu
    have hBu : G.molecule.IsBlock S u.upper u.lower := hat ▸ u.isBlock
    have hnroot := whole_unit_nonroot U hS hsk hu
    obtain ⟨a, b, hvc⟩ := U.whole_vc hsk (fun he => by rw [he] at hu; exact List.not_mem_nil hu)
    refine ⟨L, hs, ?_⟩
    intro ⟨T, p, q⟩ ht
    have hncn := spine_noCN hs u.isBlock (Or.inl u.cl) (T, p, q) ht
    obtain ⟨c, hc, he, _⟩ := Fama.member_mem_vinesV hS ⟨a, b, hvc⟩ hBu
      (hat ▸ hs.ingredient_of_mem ht) hncn (Or.inl hnroot)
    exact ⟨c, hc, he⟩
  | some sk =>
    have hr := skip_runs_selected U hS sk hsk
    have take_run {R : Finset (GBranch G.tree)} {a b : GBranch G.tree}
        (hat : u.atoms = R)
        (hc : R = ∅ ∨ ∃ LL, Fama.Spine γ G.molecule LL R a b ∧
          ∀ t ∈ LL, ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1)
        (hj : u.upper = a ∧ u.lower = b ∨ u.upper = b ∧ u.lower = a) :
        ∃ L, Fama.Spine γ G.molecule L u.atoms u.upper u.lower ∧
          ∀ t ∈ L, ∃ c ∈ vinesVG γ G, c.atoms = t.1 := by
      have hne : R ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm; exact Finset.notMem_empty u.upper hm
      obtain ⟨LL, hs, hsel⟩ := hc.resolve_left hne
      have hmem : ∀ t ∈ LL, ∃ c ∈ vinesVG γ G, c.atoms = t.1 := by
        intro t ht; obtain ⟨c, hc, he, _⟩ := hsel t ht; exact ⟨c, hc, he⟩
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨LL, by rw [hat, hup, hlo]; exact hs, hmem⟩
      · obtain ⟨RR, hsR, hmemR⟩ := selected_spine_reverse hs hmem
        exact ⟨RR, by rw [hat, hup, hlo]; exact hsR, hmemR⟩
    rcases (U.skip_units sk hsk).1 u hu with ⟨hat, hj⟩ | ⟨hat, hj⟩
    · exact take_run hat hr.1 hj
    · exact take_run hat hr.2 hj

end WaveTurbulence.GammaLow.Famc.VineA
