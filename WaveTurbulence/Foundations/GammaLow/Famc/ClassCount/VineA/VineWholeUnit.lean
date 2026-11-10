/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Vine.A.VineWholeUnit` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.Vine.A.VineWholeUnit
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
/-! A whole-group unit has a nonroot VC group. Soundness at the upper
joint excludes the top-ingredient omission in a root VC. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- Every CL ingredient containing the upper joint of a CL Fama.chain is its top ingredient. -/
theorem containing_upper_top {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Fama.Spine γ G.molecule L S a b) (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) {c : CLVineG γ G}
    (hi : IsIngredientG γ G.molecule S c.atoms) (ha : a ∈ c.atoms) : IsTopIngredientG S c := by
  have hM := garden_isMolecule G
  have hn := spine_noCN hs hB (Or.inl hCL)
  have hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p := by
    intro T p q hm
    rcases Fama.vine_cl_or_cn (hs.mem_vine hm).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn _ hm h).elim
  obtain ⟨h1, _, h3⟩ := hs.cl_aligned hM hcl hB hCL.1
  have Fama.joints (d : CLVineG γ G) (hd : IsIngredientG γ G.molecule S d.atoms) :
      ∃ q, (d.atoms, d.upper, q) ∈ L := by
    obtain ⟨p, q, hm | hm⟩ := Fama.isIngredient_vc hM hB hs hd
    · have hp := (h1 _ _ _ hm).1
      have e : d.upper = p := Fama.clvine_upper_eq (c' := ⟨d.atoms, p, q, (hs.mem_vine hm).1, hp.1, hp.2⟩) rfl
      exact ⟨q, e.symm ▸ hm⟩
    · have hp := (h1 _ _ _ hm).1
      have e : d.upper = q := Fama.clvine_upper_eq (c' := ⟨d.atoms, q, p, (hs.mem_vine hm).1, hp.1, hp.2⟩) rfl
      exact ⟨p, e.symm ▸ hm⟩
  obtain ⟨q, hm⟩ := Fama.joints c hi
  have hu : c.upper = a := (h1 _ _ _ hm).2.2 ha
  intro c' hi' hne
  obtain ⟨q', hm'⟩ := Fama.joints c' hi'
  have hdesc := (h1 _ _ _ hm').2.1
  have hne' : a ≠ c'.upper := by
    intro he
    have hm0 : (c.atoms, a, q) ∈ L := hu ▸ hm
    have hm1 : (c'.atoms, a, q') ∈ L := he.symm ▸ hm'
    exact hne (h3 _ _ _ _ hm1 hm0)
  rw [hu]
  exact ⟨hne', hdesc⟩

/-- An actual whole-group unit is not a root VC. -/
theorem whole_unit_nonroot {S : Finset (GBranch G.tree)} (U : Fama.GroupUnits γ G S)
    (hS : S ∈ maximalGroupsG γ G.molecule) (hskip : U.skip = none)
    {u : CLBlock G} (hu : u ∈ U.units) : ¬ IsRootVCG γ G S := by
  have hat := U.noskip_units hskip u hu
  obtain ⟨a, b, hvc⟩ := U.whole_vc hskip (fun he => by rw [he] at hu; exact List.not_mem_nil hu)
  obtain ⟨n, hn⟩ := hvc.2
  have hBu : G.molecule.IsBlock S u.upper u.lower := hat ▸ u.isBlock
  have hCu : CLParentPattern G S u.upper u.lower := hat ▸ u.cl
  have hc : ∃ c ∈ vinesVG γ G, IsIngredientG γ G.molecule S c.atoms ∧ u.upper ∈ c.atoms := by
    obtain ⟨cs, hcs, hf⟩ := U.sound u hu
    obtain ⟨T, hT, hm⟩ := (hf u.upper).mp u.isBlock.2.1
    obtain ⟨c, hcv, he, hi⟩ := hcs T hT
    exact ⟨c, hcv, he.symm ▸ hi, he.symm ▸ hm⟩
  obtain ⟨Lu, hsu⟩ := Fama.Spine.of_chain (chain_rejoint_exists hvc.1 ⟨n, hn⟩ hBu).choose_spec
  obtain ⟨c, hcv, hci, hau⟩ := hc
  have htop := containing_upper_top hsu hBu hCu hci hau
  intro hroot
  obtain ⟨S', hS', hi', hcond⟩ := hcv
  have heS := Fama.group_eq_of_ingredient (garden_isMolecule G) hS' hS hi' hci
  subst S'
  rcases hcond with ⟨_, _, _, hnot⟩ | ⟨_, hcn | hnot⟩
  · exact hnot hroot
  · obtain ⟨T, hTi, x, y, hv, hpx, hpy⟩ := hcn
    obtain ⟨p, q, hm | hm⟩ := Fama.isIngredient_vc (garden_isMolecule G) hBu hsu hTi
    all_goals
      have hj := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hv) (Src.isBlock_of_isSomeVine (hsu.mem_vine hm).1)
      apply (spine_noCN hsu hBu (Or.inl hCu) _ hm)
      rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hpx, hpy⟩
      · exact ⟨hpy, hpx⟩
  · exact hnot htop

end WaveTurbulence.GammaLow.Famc.VineA
