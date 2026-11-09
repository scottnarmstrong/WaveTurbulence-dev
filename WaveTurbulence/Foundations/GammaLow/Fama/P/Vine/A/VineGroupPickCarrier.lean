/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineGroupPickCarrier` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
/-! R83 single-HV and pure-DV candidate carriers and their literal survival. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The maximal single-HV case, before any prescription is supplied. -/
def SingleHVGroup (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  S ∈ maximalGroupsG γ G.molecule ∧ (∃ a b, Src.IsHV γ G.molecule S a b) ∧
    ¬ ∃ a b, Src.IsHVC γ G.molecule S a b

/-- The maximal pure-DV case, excluding all HV/VC/HVC presentations. -/
def PureDVGroup (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  S ∈ maximalGroupsG γ G.molecule ∧ (∃ a b, Src.IsDV γ G.molecule S a b) ∧
    ¬ ∃ a b, Src.IsHV γ G.molecule S a b ∨ Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b

/-- All valid deleted-bond triples, including both joint orders and dart orientations. -/
def HVCandidate (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree))
    (t : GBranch G.tree × GBranch G.tree × GardenDart G) : Prop :=
  G.molecule.ends t.2.2 = s(t.1, t.2.1) ∧
    Src.IsSomeVine γ (eraseBond G.molecule t.2.2) S t.1 t.2.1


/-- All valid ordered constituent triples of a DV′ group (D11 `IsDVPrime`: `σ(a, b) = 1` and two members of `𝒱_γ`
with joints `a, b` meeting exactly in the joints). Main's `DVCandidate` over `𝒱_γ`, with the `σ` condition. -/
def DVCandidate (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree))
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) : Prop :=
  G.molecule.sigma t.2.1 t.2.2 = 1 ∧ ∃ B, Src.IsSomeVine γ G.molecule t.1 t.2.1 t.2.2 ∧
    Src.IsSomeVine γ G.molecule B t.2.1 t.2.2 ∧ t.1 ∩ B = {t.2.1, t.2.2} ∧ S = t.1 ∪ B

/-- Every single-HV case has a candidate. -/
theorem SingleHVGroup.candidate {S : Finset (GBranch G.tree)} (h : SingleHVGroup γ G S) :
    Nonempty {t // HVCandidate γ G S t} := by
  obtain ⟨a, b, e, he, hv⟩ := h.2.1
  exact ⟨⟨(a, b, e), he, hv⟩⟩

/-- Every pure-DV case has a candidate. -/
theorem PureDVGroup.candidate {S : Finset (GBranch G.tree)} (h : PureDVGroup γ G S) :
    Nonempty {t // DVCandidate γ G S t} := by
  obtain ⟨a, b, hσ, A, B, hA, hB, hI, hS⟩ := h.2.1
  exact ⟨⟨(A, a, b), hσ, B, hA, hB, hI, hS⟩⟩

/-- Ingredients certify a VC or HVC presentation of their group. -/
theorem ingredient_vc_or_hvc {S A : Finset (GBranch G.tree)} (h : IsIngredientG γ G.molecule S A) :
    ∃ a b, Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b := by
  rcases h with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, he, hn, hB, hI⟩
  · exact ⟨a, b, Or.inl ⟨hB, n, chain_ofVine (chainIngredientG_spec hI).1⟩⟩
  · exact ⟨a, b, Or.inr ⟨e, he, hB, n, hn, chain_ofVine (chainIngredientG_spec hI).1⟩⟩

/-- No actual unit belongs to a pure-DV group. -/
theorem PureDVGroup.units_empty {S : Finset (GBranch G.tree)} (h : PureDVGroup γ G S) :
    (groupUnitsOf γ G S).units = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  obtain ⟨cs, hcs, hiff⟩ := (groupUnitsOf γ G S).sound u hu
  obtain ⟨c, hc, _⟩ := (hiff u.upper).mp u.isBlock.2.1
  obtain ⟨c', _, _, hi⟩ := hcs c hc
  obtain ⟨a, b, hkind⟩ := ingredient_vc_or_hvc hi
  exact h.2.2 ⟨a, b, Or.inr hkind⟩

/-- Pure-DV atoms are untouched by any prescription's actual unit list. -/
theorem PureDVGroup.no_unit {S : Finset (GBranch G.tree)} (h : PureDVGroup γ G S)
    (σ : Prescription G) {v : GBranch G.tree} (hv : v ∈ S) : ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms := by
  intro u hu hvu
  obtain ⟨T, hT, _, hu⟩ := mem_unitBlocks.mp hu
  by_cases he : T = S
  · subst T
    rw [h.units_empty] at hu
    exact List.not_mem_nil hu
  · exact Finset.disjoint_left.mp (groups_disjoint (garden_isMolecule G) hT h.1 he)
      ((groupUnitsOf γ G T).sub u hu hvu) hv

/-- All single-HV atoms survive the sigma-independent normalization literally. -/
theorem SingleHVGroup.cls_none {S : Finset (GBranch G.tree)} (h : SingleHVGroup γ G S)
    {v : GBranch G.tree} (hv : v ∈ S) : (coarseSplice γ G).cls v = none :=
  stSt_cls_none (garden_isMolecule G) (fun _ => .SG)
    (no_unit_hv (garden_isMolecule G) (fun _ => .SG) h.1 h.2.1 h.2.2 hv)

/-- All pure-DV atoms survive the sigma-independent normalization literally. -/
theorem PureDVGroup.cls_none {S : Finset (GBranch G.tree)} (h : PureDVGroup γ G S)
    {v : GBranch G.tree} (hv : v ∈ S) : (coarseSplice γ G).cls v = none :=
  stSt_cls_none (garden_isMolecule G) (fun _ => .SG) (h.no_unit (fun _ => .SG) hv)

end WaveTurbulence.GammaLow.Fama.VineA
