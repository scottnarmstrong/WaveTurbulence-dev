/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.Classes` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ClassBound
public import WaveTurbulence.Foundations.Stage1.ClassCount.KeyCount
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.Classes
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainSum
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Layout
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.RootDef
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SpliceLayer
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCL
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitLinks
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitSum
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.WeightSum


/-!
# CLASSCOUNT: the classification data (σ-classes, keys) and their cardinalities

* the prescription `σ` enters the piece only through `Fama.unitBlocks γ S σ`, hence through the set of groups with `σ = SG`
  (at most `2^n` classes);
* the numbers of nonempty replacement slots, ingredient triples and ladders are bounded by `D.size`, `n`, `ρ`.
-/

@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs] [Fact LayervineTVineImproved] [Fact LayervineTVineFirst]

variable {w : ℕ}

theorem card_groupsFinset_le (S : Garden w) :
    (Fama.groupsFinset γ S).card ≤ Fintype.card (GBranch S.tree) := by
  classical
  have hM := Mole.garden_isMolecule S
  have hP := maximalGroupsG_partition (γ := γ) hM
  have hdisj : (maximalGroupsG γ S.molecule).Pairwise (fun T T' => Disjoint T T') := hP.2.1
  have hne : ∀ T ∈ Fama.groupsFinset γ S, T.Nonempty := fun T hT =>
    IsStage1GroupG.nonempty (Fama.mem_groupsFinset.1 hT).1
  have := card_le_of_disjoint_nonempty (I := {T // T ∈ Fama.groupsFinset γ S}) (fun T => T.1)
    (fun T => hne T.1 T.2) (fun T T' h => hdisj (Fama.mem_groupsFinset.1 T.2) (Fama.mem_groupsFinset.1 T'.2)
      (fun h' => h (Subtype.ext h')))
  simpa using this

/-- B1b (Mk-general form of `unitBlocks_eq_of_filter_eq`). -/
theorem unitBlocks_eq_of_filter_eqMk (S : Garden w) (σ σ' : Prescription S)
    (h : (Fama.groupsFinset γ S).filter (fun T => σ T = Molecule.GapKind.SG) =
      (Fama.groupsFinset γ S).filter (fun T => σ' T = Molecule.GapKind.SG)) {Mk : Set (CLVineG γ _)} :
    Fama.unitBlocks γ (Mk := Mk) S σ = Fama.unitBlocks γ (Mk := Mk) S σ' := by
  classical
  have hsg : Fama.sgGroups γ S σ = Fama.sgGroups γ S σ' := by
    unfold Fama.sgGroups
    refine List.filter_congr fun T hT => ?_
    have hT' : T ∈ Fama.groupsFinset γ S := Finset.mem_toList.1 hT
    have : (T ∈ (Fama.groupsFinset γ S).filter (fun T => σ T = Molecule.GapKind.SG)) ↔
        (T ∈ (Fama.groupsFinset γ S).filter (fun T => σ' T = Molecule.GapKind.SG)) := by rw [h]
    simp only [Finset.mem_filter, hT', true_and] at this
    simpa using this
  unfold Fama.unitBlocks
  rw [hsg]

theorem unitBlocks_eq_of_filter_eq (S : Garden w) (σ σ' : Prescription S)
    (h : (Fama.groupsFinset γ S).filter (fun T => σ T = Molecule.GapKind.SG) =
      (Fama.groupsFinset γ S).filter (fun T => σ' T = Molecule.GapKind.SG)) :
    Fama.unitBlocks γ S σ = Fama.unitBlocks γ S σ' := unitBlocks_eq_of_filter_eqMk (Mk := ∅) S σ σ' h

theorem incoherencyIndex_ladderGroups {α : Type*} (layer : α → ℕ) {m : ℕ} (u v : Fin (m + 1) → α) :
    incoherencyIndex layer (ladderGroups u v) = ∑ j : Fin (m + 1), if layer (u j) = layer (v j) then 0 else 1 := by
  classical
  unfold incoherencyIndex ladderGroups
  rw [length_filter_eq_sum, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, GroupCoherent]
  by_cases h : layer (u j) = layer (v j)
  · simp [h]
  · simp only [h, if_false]
    have : ¬ (∀ x ∈ [u j, v j], ∀ y ∈ [u j, v j], layer x = layer y) := by
      intro hh; exact h (hh (u j) (by simp) (v j) (by simp))
    simp only [this, decide_false, if_false] ; simp

/-- B1b (Mk-general form of `gbar_decomp`). -/
theorem gbar_decompMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) {Mk : Set (CLVineG γ _)} :
    (Fama.stage1PieceOf γ (Mk := Mk) d hS LG hd σ).gbar = ∑ s, slotInc D hS LG s +
      ∑ T ∈ (Set.toFinite (Fama.unitIngredients γ (Mk := Mk) S σ)).toFinset, Fama.vineIncoh γ S (coreOf D hS LG) T +
      ∑ i : {T // T ∈ (Fama.stSt γ (Mk := Mk) S σ).G.molecule.maximalLadders},
        incoherencyIndex (coreOf D hS LG ∘ (Fama.stSt γ (Mk := Mk) S σ).M.ob)
          (ladderGroups ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).upper i) ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).lower i)) := by
  unfold Fama.Stage1PieceGD.gbar Fama.Stage1PieceGD.gsb
  simp only [Fama.stage1PieceOf, Fama.gskOf]
  rw [gregOf_eq_sum D hS hd, ← coreOf_eq D hS hd]
  unfold LGSpine.SourceMaximalLadderData.totalIncoherency
  have : ∀ i : {T // T ∈ (Fama.stSt γ (Mk := Mk) S σ).G.molecule.maximalLadders},
      LGSpine.sourceLadderIncoherency (Fama.stSt γ (Mk := Mk) S σ).G ((Fama.stSt γ (Mk := Mk) S σ).layer (coreOf D hS LG))
        ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).upper i) ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).lower i) =
      incoherencyIndex (coreOf D hS LG ∘ (Fama.stSt γ (Mk := Mk) S σ).M.ob)
          (ladderGroups ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).upper i) ((Fama.ladderDataOf (Fama.stSt γ (Mk := Mk) S σ).G).lower i)) := by
    intro i
    rw [incoherencyIndex_ladderGroups]
    rfl
  rw [Finset.sum_congr rfl fun i _ => this i]

/-- **`ḡ` of a piece is `Σ gs + (vine incoherencies) + Σ γl`.** -/
theorem gbar_decomp {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (Fama.stage1PieceOf γ d hS LG hd σ).gbar = ∑ s, slotInc D hS LG s +
      ∑ T ∈ (Set.toFinite (Fama.unitIngredients γ S σ)).toFinset, Fama.vineIncoh γ S (coreOf D hS LG) T +
      ∑ i : {T // T ∈ (Fama.stSt γ S σ).G.molecule.maximalLadders},
        incoherencyIndex (coreOf D hS LG ∘ (Fama.stSt γ S σ).M.ob)
          (ladderGroups ((Fama.ladderDataOf (Fama.stSt γ S σ).G).upper i) ((Fama.ladderDataOf (Fama.stSt γ S σ).G).lower i)) := gbar_decompMk (Mk := ∅) d hS LG hd σ

/-- B1b (Mk-general form of `stSt_eq_of_unitBlocks_eq`). -/
theorem stSt_eq_of_unitBlocks_eqMk (S : Garden w) (σ σ' : Prescription S)
    {Mk : Set (CLVineG γ _)} (h : Fama.unitBlocks γ (Mk := Mk) S σ = Fama.unitBlocks γ (Mk := Mk) S σ') : Fama.stSt γ (Mk := Mk) S σ = Fama.stSt γ (Mk := Mk) S σ' := by
  unfold Fama.stSt; rw [h]

theorem stSt_eq_of_unitBlocks_eq (S : Garden w) (σ σ' : Prescription S)
    (h : Fama.unitBlocks γ S σ = Fama.unitBlocks γ S σ') : Fama.stSt γ S σ = Fama.stSt γ S σ' := stSt_eq_of_unitBlocks_eqMk (Mk := ∅) S σ σ' h

/-- B1b (Mk-general form of `unitIngredients_eq_of_unitBlocks_eq`). -/
theorem unitIngredients_eq_of_unitBlocks_eqMk (S : Garden w) (σ σ' : Prescription S)
    {Mk : Set (CLVineG γ _)} (h : Fama.unitBlocks γ (Mk := Mk) S σ = Fama.unitBlocks γ (Mk := Mk) S σ') : Fama.unitIngredients γ (Mk := Mk) S σ = Fama.unitIngredients γ (Mk := Mk) S σ' := by
  unfold Fama.unitIngredients; rw [h]

theorem unitIngredients_eq_of_unitBlocks_eq (S : Garden w) (σ σ' : Prescription S)
    (h : Fama.unitBlocks γ S σ = Fama.unitBlocks γ S σ') : Fama.unitIngredients γ S σ = Fama.unitIngredients γ S σ' := unitIngredients_eq_of_unitBlocks_eqMk (Mk := ∅) S σ σ' h

/-- The `ḡ`-decomposition as a function of the splice Fama.VineA.PrimeData.state γ and the ingredient set. -/
noncomputable def gbarRHS (γ : ℝ) [Fact (γ ≤ 1 / 2)] {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (st : SpState S) (ing : Finset (Finset (GBranch S.tree))) : ℕ :=
  ∑ s, slotInc D hS LG s + ∑ T ∈ ing, Fama.vineIncoh γ S (coreOf D hS LG) T +
    ∑ i : {T // T ∈ st.G.molecule.maximalLadders},
      incoherencyIndex (coreOf D hS LG ∘ st.M.ob)
        (ladderGroups ((Fama.ladderDataOf st.G).upper i) ((Fama.ladderDataOf st.G).lower i))

/-- B2d: `ḡ` of a piece at a marked set, as a function of the splice Fama.VineA.PrimeData.state γ and the ingredient set. -/
theorem gbar_eq_gbarRHSMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    (Fama.stage1PieceOf γ d hS LG hd σ Mk).gbar =
      gbarRHS γ D hS LG (Fama.stSt γ S σ Mk) (Set.toFinite (Fama.unitIngredients γ S σ Mk)).toFinset :=
  gbar_decompMk (Mk := Mk) d hS LG hd σ

theorem gbar_eq_gbarRHS {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S} (hS : S.IsPlain)
    (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    (Fama.stage1PieceOf γ d hS LG hd σ).gbar =
      gbarRHS γ D hS LG (Fama.stSt γ S σ) (Set.toFinite (Fama.unitIngredients γ S σ)).toFinset :=
  gbar_eq_gbarRHSMk d hS LG hd σ ∅

theorem rbarOf_eqMk (S : Garden (2 * w)) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    rbarOfMkG γ S σ Mk = (Fama.stSt γ S σ Mk).G.molecule.rho + (Fama.stSt γ S σ Mk).hinges.card := rfl

theorem rbarOf_eq (S : Garden (2 * w)) (σ : Prescription S) :
    rbarOfG γ S σ = (Fama.stSt γ S σ).G.molecule.rho + (Fama.stSt γ S σ).hinges.card := rbarOf_eqMk S σ ∅

/-- B2d: the piece data `(ḡ, ρ̄)` depend on the prescription and the marked set only through the unit list. -/
theorem gbar_rbar_eq_of_unitBlocks_eqMk {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ σ' : Prescription S)
    (Mk Mk' : Set (CLVineG γ S)) (h : Fama.unitBlocks γ S σ Mk = Fama.unitBlocks γ S σ' Mk') :
    (Fama.stage1PieceOf γ d hS LG hd σ Mk).gbar = (Fama.stage1PieceOf γ d hS LG hd σ' Mk').gbar ∧
      rbarOfMkG γ S σ Mk = rbarOfMkG γ S σ' Mk' := by
  have hst : Fama.stSt γ S σ Mk = Fama.stSt γ S σ' Mk' := by unfold Fama.stSt; rw [h]
  have hing : Fama.unitIngredients γ S σ Mk = Fama.unitIngredients γ S σ' Mk' := by unfold Fama.unitIngredients; rw [h]
  have hfin : (Set.toFinite (Fama.unitIngredients γ S σ Mk)).toFinset =
      (Set.toFinite (Fama.unitIngredients γ S σ' Mk')).toFinset := by
    ext T; simp [hing]
  refine ⟨?_, ?_⟩
  · rw [gbar_eq_gbarRHSMk, gbar_eq_gbarRHSMk, hfin, hst]
  · rw [rbarOf_eqMk, rbarOf_eqMk, hst]

theorem gbar_rbar_eq_of_unitBlocks_eq {R : ℕ} (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ σ' : Prescription S)
    (h : Fama.unitBlocks γ S σ = Fama.unitBlocks γ S σ') :
    (Fama.stage1PieceOf γ d hS LG hd σ).gbar = (Fama.stage1PieceOf γ d hS LG hd σ').gbar ∧ rbarOfG γ S σ = rbarOfG γ S σ' := by
  have hst := stSt_eq_of_unitBlocks_eq S σ σ' h
  have hing := unitIngredients_eq_of_unitBlocks_eq S σ σ' h
  have hfin : (Set.toFinite (Fama.unitIngredients γ S σ)).toFinset = (Set.toFinite (Fama.unitIngredients γ S σ')).toFinset := by
    ext T; simp [hing]
  refine ⟨?_, ?_⟩
  · rw [gbar_eq_gbarRHS, gbar_eq_gbarRHS, hfin]
    rw [hst]
  · rw [rbarOf_eq, rbarOf_eq, hst]

/-- B1b (Mk-general form of `length_le_hinges`). -/
theorem length_le_hingesMk (S : Garden w) (σ : Prescription S) {Mk : Set (CLVineG γ _)} :
    (Fama.unitBlocks γ (Mk := Mk) S σ).length ≤ (Fama.stSt γ (Mk := Mk) S σ).hinges.card := by
  classical
  have hM := Mole.garden_isMolecule S
  have hpair := List.pairwise_iff_get.mp (Fama.unitBlocks_pairwiseMk (Mk := Mk) hM σ)
  have hrange : ∀ j : Fin (Fama.unitBlocks γ (Mk := Mk) S σ).length, ∃ c, (Fama.stSt γ (Mk := Mk) S σ).M.ob c = ((Fama.unitBlocks γ (Mk := Mk) S σ).get j).upper := by
    intro j
    rw [(Fama.stSt γ (Mk := Mk) S σ).M.ob_range]
    right
    rw [Fama.stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) ((Fama.unitBlocks γ (Mk := Mk) S σ).get j).isBlock.2.1]
  choose c hc using hrange
  have hmem : ∀ j, c j ∈ (Fama.stSt γ (Mk := Mk) S σ).hinges := by
    intro j
    rw [SpState.mem_hinges, hc j, Fama.stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) ((Fama.unitBlocks γ (Mk := Mk) S σ).get j).isBlock.2.1]
    simp
  calc (Fama.unitBlocks γ (Mk := Mk) S σ).length = Fintype.card (Fin (Fama.unitBlocks γ (Mk := Mk) S σ).length) := (Fintype.card_fin _).symm
    _ ≤ (Fama.stSt γ (Mk := Mk) S σ).hinges.card := by
        refine Finset.card_le_card_of_injOn c (fun j _ => hmem j) ?_
        intro j _ j' _ h
        by_contra hne
        have hd : Disjoint ((Fama.unitBlocks γ (Mk := Mk) S σ).get j).atoms ((Fama.unitBlocks γ (Mk := Mk) S σ).get j').atoms := by
          rcases lt_or_gt_of_ne hne with h' | h'
          · exact hpair j j' h'
          · exact (hpair j' j h').symm
        have hu := congrArg (Fama.stSt γ (Mk := Mk) S σ).M.ob h
        rw [hc j, hc j'] at hu
        exact Finset.disjoint_left.1 hd ((Fama.unitBlocks γ (Mk := Mk) S σ).get j).isBlock.2.1 (hu ▸ ((Fama.unitBlocks γ (Mk := Mk) S σ).get j').isBlock.2.1)

theorem length_le_hinges (S : Garden w) (σ : Prescription S) :
    (Fama.unitBlocks γ S σ).length ≤ (Fama.stSt γ S σ).hinges.card := length_le_hingesMk (Mk := ∅) S σ

/-- B2d: `ρ_sb + #units ≤ ρ̄` at any marked set. -/
theorem rho_add_length_le_rbarOfMk (S : Garden (2 * w)) (σ : Prescription S) (Mk : Set (CLVineG γ S)) :
    (Fama.stSt γ S σ Mk).G.molecule.rho + (Fama.unitBlocks γ S σ Mk).length ≤ rbarOfMkG γ S σ Mk := by
  rw [rbarOf_eqMk]
  have := length_le_hingesMk (Mk := Mk) S σ
  omega

theorem rho_add_length_le_rbarOf (S : Garden (2 * w)) (σ : Prescription S) :
    (Fama.stSt γ S σ).G.molecule.rho + (Fama.unitBlocks γ S σ).length ≤ rbarOfG γ S σ :=
  rho_add_length_le_rbarOfMk S σ ∅

/-- B2d: the number of ingredient triples is at most the number of atoms (any marked set). -/
theorem card_tripI_leMk {S : Garden w} {σ : Prescription S} {Mk : Set (CLVineG γ S)} {Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ Mk).get j).atoms
          ((Fama.unitBlocks γ S σ Mk).get j).upper ((Fama.unitBlocks γ S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) :
    Fintype.card (TripIMk γ S σ Mk Tss) ≤ Fintype.card (GBranch S.tree) :=
  card_le_of_disjoint_nonempty (fun i : TripIMk γ S σ Mk Tss => (tauMk γ Tss i).1.erase (tauMk γ Tss i).2.1)
    (fun i => tau_nonemptyMk h1 i) (fun i i' hne => tau_disjointMk h1 h2 hne)

theorem card_tripI_le {S : Garden w} {σ : Prescription S} {Tss : Fin (Fama.unitBlocks γ S σ).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ).get j).atoms
          ((Fama.unitBlocks γ S σ).get j).upper ((Fama.unitBlocks γ S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) :
    Fintype.card (TripI γ S σ Tss) ≤ Fintype.card (GBranch S.tree) :=
  card_tripI_leMk (Mk := ∅) h1 h2

end WaveTurbulence.GammaLow.Famc.ClassCount
