/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.Slots2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
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


/-!
# CLASSCOUNT: the slot incoherency is the `Fama.gregOf` summand

For an embedded regular couple/tree, the list of links has no repetition and its endpoints are branching nodes, so
`LayeredGarden.incoherency` (a count of branch pairs) agrees with `incohCount` (a count along the list).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LFTwist RegRed WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

theorem chainEmb_links_branching {G : Garden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) {l : (Fin w × Path) × (Fin w × Path)} (hl : l ∈ X.linksAt ζ a) :
    l.1.2 ∈ (G.tree l.1.1).branching ∧ l.2.2 ∈ (G.tree l.2.1).branching := by
  have key : ∀ x ∈ pairEndpoints (X.linksAt ζ a), x.2 ∈ (G.tree x.1).branching := by
    intro x hx
    have h1 : x ∈ branchAddresses (X.plug ζ h) a := by
      rw [chain_branchAddresses]; exact Finset.mem_union_left _ hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h1
    exact ((node_iff_of_subtree hC.node hC.tree q).2.2).2 hq
  exact ⟨key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
    key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)⟩

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The slot incoherency (counted along the link list) is the summand of `Fama.gregOf`. -/
theorem slotInc_eq {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) (s : ReplacementSlot S) :
    LG.incoherency (match s with
      | .inl p => (D.couple p).linksAt (cplA D hS p) (cplB D hS p)
      | .inr b => (D.tree b).linksAt (nodeSign S.sig b.1) (treeA D b)) = slotInc D hS LG s := by
  cases s with
  | inl p =>
    have hE := reconstruction_coupleEmb D hS hd p
    exact incoherency_eq_count_of LG _ (nodup_of_flat_nodup (couple_linksAt_flat_nodup _ _ _ hE.indep))
      (fun l hl => embeds_links_branching hE hl)
  | inr b =>
    have hC := reconstruction_chainEmb D hS hd b
    exact incoherency_eq_count_of LG _ (nodup_of_flat_nodup (chain_linksAt_flat_nodup _ _ _))
      (fun l hl => chainEmb_links_branching hC hl)

/-- `Fama.gregOf` is the sum of the slot incoherencies. -/
theorem gregOf_eq_sum {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) :
    Fama.gregOf D hS LG = ∑ s, slotInc D hS LG s := by
  classical
  rw [Fintype.sum_sum_type]
  unfold Fama.gregOf
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact slotInc_eq D hS hd (.inl p)
  · refine Finset.sum_congr rfl fun b _ => ?_
    exact slotInc_eq D hS hd (.inr b)

/-- **Class bound.**  Layered gardens decoded by `D` with a common slot-incoherency vector `gs`. -/
theorem card_class_le (p : ℕ) (gs : ReplacementSlot S → ℕ) (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ D.Decodes hS LG.garden ∧
      ∀ s, slotInc D hS LG s = gs s) :
    (A.card : ℝ) ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size *
      ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s) := by
  classical
  have hfib : A.card = ∑ f ∈ A.image (coreOf D hS), (A.filter (fun LG => coreOf D hS LG = f)).card :=
    Finset.card_eq_sum_card_image (coreOf D hS) A
  have hb : ∀ f ∈ A.image (coreOf D hS), ((A.filter (fun LG => coreOf D hS LG = f)).card : ℝ) ≤
      (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * (2 : ℝ) ^ (∑ s, slotDist hS p f s) := by
    intro f _
    have h := card_slot_bound D hS p f gs (A.filter (fun LG => coreOf D hS LG = f)) (by
      intro LG hLG
      obtain ⟨hLA, hf⟩ := Finset.mem_filter.1 hLG
      obtain ⟨hc, hp, hd, hinc⟩ := hA LG hLA
      exact ⟨hc, hp, hd, by rw [← coreOf_eq D hS hd]; exact hf, hinc⟩)
    rw [prod_slotBound] at h
    exact_mod_cast h
  rw [hfib, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  exact hb f hf

end WaveTurbulence.GammaLow.Famc.ClassCount
