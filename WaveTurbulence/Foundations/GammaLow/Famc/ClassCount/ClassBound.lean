/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.ClassBound` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.WeightSum
public import WaveTurbulence.Foundations.Stage1.ClassCount.SRCount
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.RootDef
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.ClassBound
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
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


/-!
# CLASSCOUNT: the bound for one class of layered gardens

For fixed `(S, D, σ)`, `p`, slot incoherencies `gs`, per-ingredient incoherencies `gfix` and per-ladder incoherencies
`γl`, the number of canonical layered gardens decoded by `D` with these data is at most
`2^{|D|} K0^{4n} (K0^{p+1})^{24 ρ̄ + 17 g}`, `g = Σ gs + V + Σ γl` (TARGET L2248-L2252, with the run/bad accounting of
`ChainSum`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs] [Fact LayervineTVineImproved] [Fact LayervineTVineFirst]

variable {w : ℕ}

/-- B2d: the index of the canonical ingredient triples of all units at the marked set `Mk`. -/
abbrev TripIMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (S : Garden w) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S)) : Type :=
  Σ j : Fin (Fama.unitBlocks γ S σ Mk).length, Fin (Tss j).length

/-- B2d: the ingredient triple of an index (marked set `Mk`). -/
def tauMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] {S : Garden w} {σ : Prescription S} {Mk : Set (CLVineG γ S)}
    (Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S))
    (i : TripIMk γ S σ Mk Tss) : Trip S := (Tss i.1).get i.2

section tripfactsMk
variable {S : Garden w} {σ : Prescription S} {Mk : Set (CLVineG γ S)} {Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S)}
  (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ Mk).get j).atoms
          ((Fama.unitBlocks γ S σ Mk).get j).upper ((Fama.unitBlocks γ S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
  (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)

include h1 in
theorem tau_specMk (i : TripIMk γ S σ Mk Tss) :
    (tauMk γ Tss i).1 ⊆ ((Fama.unitBlocks γ S σ Mk).get i.1).atoms ∧ (tauMk γ Tss i).2.1 ∈ (tauMk γ Tss i).1 ∧
      (tauMk γ Tss i).2.2 ∈ (tauMk γ Tss i).1 ∧ (tauMk γ Tss i).2.1 ≠ (tauMk γ Tss i).2.2 ∧
      (tauMk γ Tss i).1 ∈ Fama.unitIngredients γ S σ Mk := by
  obtain ⟨n, hn⟩ := h1 i.1
  have hi := (hn _ (List.get_mem (Tss i.1) i.2)).1
  have hsp := chainIngredientG_spec hi
  have hXb := Src.isBlock_of_isSomeVine hsp.2.1
  refine ⟨hsp.2.2, hXb.2.1, hXb.2.2.1, hXb.2.2.2.1, ?_⟩
  exact ⟨(Fama.unitBlocks γ S σ Mk).get i.1, List.get_mem _ _, _, _, n, _, _, hi⟩

include h1 h2 in
theorem tau_disjointMk {i i' : TripIMk γ S σ Mk Tss} (hne : i ≠ i') :
    Disjoint ((tauMk γ Tss i).1.erase (tauMk γ Tss i).2.1) ((tauMk γ Tss i').1.erase (tauMk γ Tss i').2.1) := by
  classical
  obtain ⟨j, k⟩ := i
  obtain ⟨j', k'⟩ := i'
  by_cases hj : j = j'
  · subst hj
    have hk : k ≠ k' := fun h => hne (by rw [h])
    have hp := List.pairwise_iff_get.mp (h2 j)
    rcases lt_or_gt_of_ne hk with h | h
    · have := hp ⟨k.1, by simp⟩ ⟨k'.1, by simp⟩ h
      simpa [tauMk] using this
    · have := hp ⟨k'.1, by simp⟩ ⟨k.1, by simp⟩ h
      simpa [tauMk] using this.symm
  · have hpair := List.pairwise_iff_get.mp (Fama.unitBlocks_pairwiseMk (Mole.garden_isMolecule S) σ Mk)
    have hU : Disjoint ((Fama.unitBlocks γ S σ Mk).get j).atoms ((Fama.unitBlocks γ S σ Mk).get j').atoms := by
      rcases lt_or_gt_of_ne hj with h | h
      · exact hpair j j' h
      · exact (hpair j' j h).symm
    exact Finset.disjoint_of_subset_left ((Finset.erase_subset _ _).trans (tau_specMk h1 ⟨j, k⟩).1)
      (Finset.disjoint_of_subset_right ((Finset.erase_subset _ _).trans (tau_specMk h1 ⟨j', k'⟩).1) hU)

include h1 in
theorem tau_nonemptyMk (i : TripIMk γ S σ Mk Tss) : ((tauMk γ Tss i).1.erase (tauMk γ Tss i).2.1).Nonempty := by
  obtain ⟨-, hx, hy, hxy, -⟩ := tau_specMk h1 i
  exact ⟨(tauMk γ Tss i).2.2, Finset.mem_erase.2 ⟨hxy.symm, hy⟩⟩

end tripfactsMk

section tripfacts
variable {S : Garden w} {σ : Prescription S} {Tss : Fin (Fama.unitBlocks γ S σ).length → List (Trip S)}
  (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ).get j).atoms
          ((Fama.unitBlocks γ S σ).get j).upper ((Fama.unitBlocks γ S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
  (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)

end tripfacts

open Classical in
/-- B2d: **the bad-ingredient exponent** at any marked set. -/
theorem E_leMk {S : Garden w} (hS : S.IsPlain) {σ : Prescription S} {Mk : Set (CLVineG γ S)} (D : ReconstructionData S) (p : ℕ)
    {Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S)}
    (h1 : ∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ Mk).get j).atoms
          ((Fama.unitBlocks γ S σ Mk).get j).upper ((Fama.unitBlocks γ S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2)
    (h2 : ∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint)
    (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, ∀ s, slotInc D hS LG s = gs s)
    (gfix : Finset (GBranch S.tree) → ℕ) :
    ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p (A.image (coreOf D hS)) gfix t)).map
        (fun t => gfix t.1 + 3)).sum ≤
      8 * ∑ T ∈ (Finset.univ : Finset (TripIMk γ S σ Mk Tss)).image (fun i => (tauMk γ Tss i).1), gfix T +
        6 * ∑ s, gs s := by
  set 𝓖 := A.image (coreOf D hS) with h𝓖
  -- convert to a sum over the index
  have hconv : ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum =
      ∑ i : TripIMk γ S σ Mk Tss, if ¬ GoodIng S hS p 𝓖 gfix (tauMk γ Tss i) then gfix (tauMk γ Tss i).1 + 3 else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [listSum_filter_eq]
    rfl
  rw [hconv]
  set RB : TripIMk γ S σ Mk Tss → Prop := fun i => ∃ s, regionHas hS (tauMk γ Tss i).1 (tauMk γ Tss i).2.1 s ∧ 1 ≤ gs s with hRB
  have hpt : ∀ i : TripIMk γ S σ Mk Tss, (if ¬ GoodIng S hS p 𝓖 gfix (tauMk γ Tss i) then gfix (tauMk γ Tss i).1 + 3 else 0) ≤
      4 * gfix (tauMk γ Tss i).1 + (if RB i then 3 else 0) := by
    intro i
    by_cases hg : GoodIng S hS p 𝓖 gfix (tauMk γ Tss i)
    · rw [if_neg (not_not.2 hg)]; omega
    · rw [if_pos hg]
      by_cases hz : gfix (tauMk γ Tss i).1 = 0
      · have hRBi : RB i := by
          by_contra hno
          apply hg
          refine ⟨?_, hz, ?_⟩
          · obtain ⟨n, hn⟩ := h1 i.1
            exact (hn _ (List.get_mem (Tss i.1) i.2)).2
          · intro f hf
            obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
            obtain ⟨hc, hd, hinc⟩ := hA LG hLG
            refine sourceRegion_of_zero hS p hc D hd _ _ (fun s hs => ?_)
            rw [hinc s]
            by_contra hne
            exact hno ⟨s, hs, by omega⟩
        rw [if_pos hRBi, hz]
      · have : 1 ≤ gfix (tauMk γ Tss i).1 := by omega
        split_ifs <;> omega
  have hsum1 : ∑ i : TripIMk γ S σ Mk Tss, (4 * gfix (tauMk γ Tss i).1 + (if RB i then 3 else 0)) =
      4 * ∑ i : TripIMk γ S σ Mk Tss, gfix (tauMk γ Tss i).1 + 3 * (Finset.univ.filter (fun i => RB i)).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    ring
  have hfib := sum_le_two_mul_of_fiber (fun i : TripIMk γ S σ Mk Tss => (tauMk γ Tss i).1) (fun i => (tauMk γ Tss i).2.1)
    (fun i => (tau_specMk h1 i).2.1) (fun i => tau_nonemptyMk h1 i) (fun i i' hne => tau_disjointMk h1 h2 hne)
    ((Finset.univ : Finset (TripIMk γ S σ Mk Tss)).image (fun i => (tauMk γ Tss i).1))
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) gfix
  have hcard := card_bad_region_le hS (fun i : TripIMk γ S σ Mk Tss => (tauMk γ Tss i).1) (fun i => (tauMk γ Tss i).2.1)
    (fun i i' hne => tau_disjointMk h1 h2 hne) gs
  calc ∑ i : TripIMk γ S σ Mk Tss, (if ¬ GoodIng S hS p 𝓖 gfix (tauMk γ Tss i) then gfix (tauMk γ Tss i).1 + 3 else 0)
      ≤ ∑ i : TripIMk γ S σ Mk Tss, (4 * gfix (tauMk γ Tss i).1 + (if RB i then 3 else 0)) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ ≤ _ := by
        have hcard' : (Finset.univ.filter (fun i => RB i)).card ≤ 2 * ∑ s, gs s := hcard
        rw [hsum1]; omega

open Classical in
/-- B2d: **the class bound** at any marked set. -/
theorem class_boundMk : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (S : Garden w) (hS : S.IsPlain) (D : ReconstructionData S)
    (σ : Prescription S) (Mk : Set (CLVineG γ S)),
    ∃ Tss : Fin (Fama.unitBlocks γ S σ Mk).length → List (Trip S),
      (∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredientG γ S.molecule ((Fama.unitBlocks γ S σ Mk).get j).atoms
          ((Fama.unitBlocks γ S σ Mk).get j).upper ((Fama.unitBlocks γ S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) ∧
      ∀ (p : ℕ) (A : Finset (LayeredGarden w)) (gs : ReplacementSlot S → ℕ)
        (γl : {T // T ∈ (stSt γ S σ Mk).G.molecule.maximalLadders} → ℕ) (V : ℕ)
        (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ ∃ hd : D.Decodes hS LG.garden, (∀ s, slotInc D hS LG s = gs s) ∧
          ∀ i, incoherencyIndex (coreOf D hS LG ∘ (stSt γ S σ Mk).M.ob)
            (ladderGroups ((Fama.ladderDataOf (stSt γ S σ Mk).G).upper i) ((Fama.ladderDataOf (stSt γ S σ Mk).G).lower i)) = γl i)
        (hconst : ∀ LG ∈ A, ∀ LG' ∈ A, ∀ i : TripIMk γ S σ Mk Tss,
          Fama.vineIncoh γ S (coreOf D hS LG) (tauMk γ Tss i).1 = Fama.vineIncoh γ S (coreOf D hS LG') (tauMk γ Tss i).1)
        (hV : ∀ LG ∈ A, ∑ T ∈ (Set.toFinite (Fama.unitIngredients γ S σ Mk)).toFinset, Fama.vineIncoh γ S (coreOf D hS LG) T ≤ V),
      (A.card : ℝ) ≤ (2 : ℝ) ^ D.size * K0 ^ (4 * Fintype.card (GBranch S.tree)) *
        (K0 ^ (p + 1)) ^ (24 * ((stSt γ S σ Mk).G.molecule.rho + (Fama.unitBlocks γ S σ Mk).length) + 15 * ∑ s, gs s +
          ∑ i, γl i + 8 * V) := by
  obtain ⟨K0, hK0, hW⟩ := weight_sum_leMk
  refine ⟨K0, hK0, ?_⟩
  intro γ _ w S hS D σ Mk
  obtain ⟨Tss, h1, h2, hmain⟩ := hW γ S hS σ Mk
  refine ⟨Tss, h1, h2, ?_⟩
  intro p A gs γl V hA hconst hV
  have hK1 : 1 ≤ K0 := by linarith
  have hK0' : 0 ≤ K0 := by linarith
  by_cases hAe : A = ∅
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨LG0, hLG0⟩ := Finset.nonempty_iff_ne_empty.2 hAe
  set 𝓖 := A.image (coreOf D hS) with h𝓖def
  set gfix : Finset (GBranch S.tree) → ℕ := fun T => Fama.vineIncoh γ S (coreOf D hS LG0) T with hgfix_def
  have h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p := by
    intro f hf
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨hc, hd, -⟩ := hA LG hLG
    refine ⟨?_, fun x => ?_⟩
    · rw [coreOf_eq D hS hd]
      exact LFTwist.inducedPrelayer_isBranchPrelayering LG D hS hd
    · rw [coreOf_eq D hS hd]; exact hc.2.2.1 _
  have hγl : ∀ f ∈ 𝓖, ∀ i, incoherencyIndex (f ∘ (stSt γ S σ Mk).M.ob)
      (ladderGroups ((Fama.ladderDataOf (stSt γ S σ Mk).G).upper i) ((Fama.ladderDataOf (stSt γ S σ Mk).G).lower i)) = γl i := by
    intro f hf i
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    exact (hA LG hLG).2.choose_spec.2 i
  have hgfix : ∀ f ∈ 𝓖, ∀ j, ∀ t ∈ Tss j, Fama.vineIncoh γ S f t.1 = gfix t.1 := by
    intro f hf j t ht
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
    exact hconst LG hLG LG0 hLG0 ⟨j, k⟩
  have hw := hmain p 𝓖 h𝓖 γl hγl gfix hgfix
  have hb1 := card_class_le_bond D hS p gs A (fun LG hLG => by
    obtain ⟨hc, hd, hinc, -⟩ := hA LG hLG
    exact ⟨hc.2.2, hc.1, hd, hinc⟩)
  have hE := E_leMk hS D p h1 h2 A gs (fun LG hLG => by
    obtain ⟨hc, hd, hinc, -⟩ := hA LG hLG
    exact ⟨hc, hd, hinc⟩) gfix
  have hYV : ∑ T ∈ (Finset.univ : Finset (TripIMk γ S σ Mk Tss)).image (fun i => (tauMk γ Tss i).1), gfix T ≤ V := by
    refine le_trans ?_ (hV LG0 hLG0)
    refine Finset.sum_le_sum_of_subset ?_
    intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT
    exact (Set.toFinite _).mem_toFinset.2 (tau_specMk h1 i).2.2.2.2
  have hrt := rootThings_leMk S hS σ Mk
  have hatoms : S.molecule.atoms = Finset.univ := rfl
  rw [hatoms] at hw
  have hEb := hE.trans (Nat.add_le_add (Nat.mul_le_mul_left 8 hYV) le_rfl)
  have hSg0 : 0 ≤ ∑ f ∈ 𝓖, (2 : ℝ) ^ (bondExp S.molecule Finset.univ f) :=
    Finset.sum_nonneg fun f _ => by positivity
  exact class_numerics hK0 hSg0 hb1 hw hEb hrt

end WaveTurbulence.GammaLow.Famc.ClassCount
