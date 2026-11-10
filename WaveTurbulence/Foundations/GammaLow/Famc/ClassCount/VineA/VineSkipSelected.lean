/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineSkipSelected` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.A.VineWholeUnit
public import WaveTurbulence.Foundations.Vine.A.VineSkipSelected
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
/-! Every non-skipped ingredient of a declared group spine is in V.
The weaker top-case record is completed using its cover property. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- The two source Fama.chain presentations have identical constructors. -/
theorem chain_toSource {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Src.Chain γ M S a b n := by
  induction h with
  | single h => exact .single h
  | append _ h hi hne ih => exact .append ih h hi hne

/-- A skipped group is an actual VC or HVC, with the declared outer Fama.joints. -/
theorem skip_group_kind {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S) :
    Src.IsVC γ G.molecule S sk.a sk.b ∨ Src.IsHVC γ G.molecule S sk.a sk.b := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    exact Or.inl ⟨sk.blockM hb, n, chain_toSource (chainIngredientG_spec hi).1⟩
  | some e =>
    obtain ⟨n, hn, hi⟩ := sk.chainN e hb
    have he := sk.blockN e hb
    exact Or.inr ⟨e, he.1, he.2, n, hn, chain_toSource (chainIngredientG_spec hi).1⟩

/-- With a CN ingredient, every CL ingredient of a VC/HVC belongs to V. -/
theorem cl_mem_vinesV_of_CN {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule)
    (hvl : ∃ a b, Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b)
    (hcn : ∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T)
    (c : CLVineG γ G) (hi : IsIngredientG γ G.molecule S c.atoms) : c ∈ vinesVG γ G := by
  refine ⟨S, hS, hi, ?_⟩
  obtain ⟨a, b, hvc | hhvc⟩ := hvl
  · by_cases hr : IsRootVCG γ G S
    · exact Or.inr ⟨Or.inr hr, Or.inl hcn⟩
    · exact Or.inl ⟨a, b, hvc, hr⟩
  · exact Or.inr ⟨Or.inl ⟨a, b, hhvc⟩, Or.inl hcn⟩

/-- All source ingredients of the declared spine except the skipped one are selected. -/
theorem skip_spine_selected {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    (hS : S ∈ maximalGroupsG γ G.molecule) (sk : Fama.SkipData γ G S) (hsk : U.skip = some sk)
    {D : Type} [Fintype D] [DecidableEq D] {N : Molecule (GBranch G.tree) D}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (hs : Fama.Spine γ N L S sk.a sk.b) (hA : (sk.A, sk.x, sk.y) ∈ L)
    (hv : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine γ G.molecule T p q)
    (hi : ∀ T p q, (T, p, q) ∈ L → IsIngredientG γ G.molecule S T) :
    ∀ t ∈ L, t.1 ≠ sk.A → ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1 := by
  have hvl : ∃ a b, Src.IsVC γ G.molecule S a b ∨ Src.IsHVC γ G.molecule S a b :=
    ⟨sk.a, sk.b, skip_group_kind sk⟩
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q ht => Src.isBlock_of_isSomeVine (hv T p q ht)
  rcases sk.kind with hcn | ⟨hroot, c0, hat, htop⟩
  · have hCN : ∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T :=
      ⟨sk.A, sk.ingredient, sk.x, sk.y, sk.vine, hcn⟩
    intro ⟨T, p, q⟩ ht hne
    have hn : ¬ CNMem G (T, p, q) := fun hc =>
      hne (congrArg Prod.fst (hs.cn_unique hblk ht hA hc hcn))
    obtain ⟨c, hc, _⟩ := Fama.exists_clVine (hv T p q ht) hn
    have hci : IsIngredientG γ G.molecule S c.atoms := hc.symm ▸ hi T p q ht
    exact ⟨c, cl_mem_vinesV_of_CN hS hvl hCN c hci, hc, hi T p q ht⟩
  · have hbase : (∃ a b, Src.IsHVC γ G.molecule S a b) ∨ IsRootVCG γ G S := by
      cases hb : sk.bond with
      | none => exact Or.inr (hroot hb)
      | some e =>
        rcases skip_group_kind sk with hvc | hvc
        · exact (Fama.vc_not_hyper hvc.1 ⟨e, (sk.blockN e hb).1, (sk.blockN e hb).2⟩).elim
        · exact Or.inl ⟨sk.a, sk.b, hvc⟩
    have hn : ∀ t ∈ L, ¬ CNMem G t := by
      intro ⟨T, p, q⟩ ht hcn
      have hCN : ∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T :=
        ⟨T, hi T p q ht, p, q, hv T p q ht, hcn⟩
      have hci : IsIngredientG γ G.molecule S c0.atoms := hat.symm ▸ sk.ingredient
      have hc0 := cl_mem_vinesV_of_CN hS hvl hCN c0 hci
      exact skipped_not_vinesV U hS sk hsk hc0 hat
    intro ⟨T, p, q⟩ ht hne
    obtain ⟨c, hc, _⟩ := Fama.exists_clVine (hv T p q ht) (hn _ ht)
    have hci : IsIngredientG γ G.molecule S c.atoms := hc.symm ▸ hi T p q ht
    have hnt : ¬ IsTopIngredientG S c := fun h => Fama.top_unique h htop hci
      (hat.symm ▸ sk.ingredient) (by rw [hc, hat]; exact hne)
    exact ⟨c, ⟨S, hS, hci, Or.inr ⟨hbase, Or.inr hnt⟩⟩, hc, hi T p q ht⟩

end WaveTurbulence.GammaLow.Famc.VineA
