/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineDVGroupKey` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import Mathlib.Data.Finset.Sort
public import WaveTurbulence.Foundations.Vine.A.VineDVGroupKey
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
/-! R83 pure-DV keys: the complete normalized constituent support and its joints. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- The constituent and the joints of a DV′ candidate lie in the group. -/
theorem DVCandidate.support {S : Finset (GBranch G.tree)} {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (h : DVCandidate γ G S t) : t.1 ⊆ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S := by
  obtain ⟨-, B, hA, _, _, hS⟩ := h
  have hsub : t.1 ⊆ S := by rw [hS]; exact Finset.subset_union_left
  have hB := Src.isBlock_of_isSomeVine hA
  exact ⟨hsub, hsub hB.2.1, hsub hB.2.2.1⟩

/-- An ordered list of every normalized atom in a support. -/
noncomputable def coarseSupportWord (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (A : Finset (GBranch G.tree)) : List (List ℕ) := by
  classical
  exact (A.image (coarseAtomWord γ G)).sort (· ≤ ·)

/-- Untouched supports are determined by their complete normalized words. -/
theorem coarseSupportWord_inj_of_none {A B : Finset (GBranch G.tree)}
    (hA : ∀ a ∈ A, (coarseSplice γ G).cls a = none)
    (hB : ∀ b ∈ B, (coarseSplice γ G).cls b = none)
    (he : coarseSupportWord γ G A = coarseSupportWord γ G B) : A = B := by
  classical
  have himg : A.image (coarseAtomWord γ G) = B.image (coarseAtomWord γ G) := by
    simpa only [coarseSupportWord, Finset.sort_toFinset] using congrArg List.toFinset he
  ext v
  constructor
  · intro hv
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp (himg ▸ Finset.mem_image_of_mem (coarseAtomWord γ G) hv)
    exact (coarseAtomWord_inj_of_none (hB b hb) (hA v hv) he) ▸ hb
  · intro hv
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (himg.symm ▸ Finset.mem_image_of_mem (coarseAtomWord γ G) hv)
    exact (coarseAtomWord_inj_of_none (hA a ha) (hB v hv) he) ▸ ha

/-- Lexicographic comparison of the sorted constituent support, then its two joints. -/
noncomputable def dvGroupKey (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) :
    List (List (List ℕ)) :=
  [coarseSupportWord γ G t.1, [coarseAtomWord γ G t.2.1], [coarseAtomWord γ G t.2.2]]

/-- On pure-DV candidates the full normalized key is injective. -/
theorem dvGroupKey_injective (hS : PureDVGroup γ G S) :
    Function.Injective (fun t : {t // DVCandidate γ G S t} => dvGroupKey γ G t.1) := by
  intro x y he
  have ha := (List.cons.inj he).1
  have hb := (List.cons.inj (List.cons.inj (List.cons.inj he).2).1).1
  have hc := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj he).2).2).1).1
  have hea : x.1.1 = y.1.1 := coarseSupportWord_inj_of_none
    (fun a ha => hS.cls_none (x.2.support.1 ha))
    (fun a ha => hS.cls_none (y.2.support.1 ha)) ha
  have heb : x.1.2.1 = y.1.2.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.support.2.1) (hS.cls_none y.2.support.2.1) hb
  have hec : x.1.2.2 = y.1.2.2 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.support.2.2) (hS.cls_none y.2.support.2.2) hc
  exact Subtype.ext (Prod.ext hea (Prod.ext heb hec))

/-- The pure-DV normalized candidate set has exactly one least triple. -/
theorem dvGroupKey_existsUnique (hS : PureDVGroup γ G S) :
    ∃! t : {t // DVCandidate γ G S t}, ∀ u : {t // DVCandidate γ G S t},
      dvGroupKey γ G t.1 ≤ dvGroupKey γ G u.1 := by
  let : Nonempty {t // DVCandidate γ G S t} := hS.candidate
  exact existsUnique_least_key _ (dvGroupKey_injective hS)

/-- R83's pure-DV constituent choice, made without a prescription. -/
noncomputable def dvGroupPick (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if hS : PureDVGroup γ G S then some (dvGroupKey_existsUnique hS).choose.1 else none

/-- The chosen DV triple is valid and least among all normalized candidates. -/
theorem dvGroupPick_spec {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (h : dvGroupPick γ G S = some t) : PureDVGroup γ G S ∧ DVCandidate γ G S t ∧
      ∀ u : {u // DVCandidate γ G S u}, dvGroupKey γ G t ≤ dvGroupKey γ G u.1 := by
  classical
  unfold dvGroupPick at h
  split_ifs at h with hS
  · have he := Option.some.inj h
    subst t
    exact ⟨hS, (dvGroupKey_existsUnique hS).choose.property, (dvGroupKey_existsUnique hS).choose_spec.1⟩

end WaveTurbulence.GammaLow.Fama.VineA
