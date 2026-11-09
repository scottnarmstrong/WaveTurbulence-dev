/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.Slots` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeCoverage
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DecodedCoreEmbedding
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2Tree
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2
public import WaveTurbulence.Foundations.IncohInst.Links.Partition
public import WaveTurbulence.Foundations.Spine.InducedLayeringFinite
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain


/-!
# CLASSCOUNT: layered gardens over a fixed skeleton and replacement datum (injection into slot traces)

For `LG` decoded by `D` over the skeleton `S`, the layering of `LG` is determined by the core layer
`coreLayer` (a function of the skeleton branches) and the *slot traces*: the restriction to the nodes of each
regular couple/tree replacement (`ReplacementSlot S`), extended by `0`.  Each trace lies in the carrier of
`Links.layerreg2` / `layerreg2_tree`, so the number of `LG` with given core layer and slot incoherencies is bounded
by the product of the `layerreg2` bounds (TARGET L2248-L2252).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LFTwist RegRed WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

variable (D : ReconstructionData S) (hS : S.IsPlain)

/-- The trace of `LG` on a slot: the layers on the nodes of the replacement, `0` elsewhere. -/
noncomputable def slotTrace (LG : LayeredGarden w) : ReplacementSlot S → (Fin w × Path → ℕ)
  | .inl p => fun z => if z ∈ cplNodes (D.couple p) (cplA D hS p) (cplB D hS p) then layerAt LG z else 0
  | .inr b => fun z => if z ∈ chainNodesSet (D.tree b) (nodeSign S.sig b.1) (treeA D b) then layerAt LG z else 0

/-- **The trace of a canonical layered garden on a slot lies in the `layerreg2` carrier.** -/
theorem slotTrace_mem {p : ℕ} {LG : LayeredGarden w} (hcan : LG.CanonCriterion p) (hpl : LG.garden.IsPlain)
    (hd : D.Decodes hS LG.garden) (s : ReplacementSlot S) :
    slotTrace D hS LG s ∈ slotCarrier D hS p (coreLayer LG D hS hd) (slotInc D hS LG s) s := by
  cases s with
  | inl pr =>
    refine ⟨LG, hcan, hpl, reconstruction_coupleEmb D hS hd pr, ?_, ?_, rfl, fun z => rfl⟩
    · exact parAt_inflated D hS LG hd p _
    · exact parAt_inflated D hS LG hd p _
  | inr b =>
    refine ⟨LG, node3 (fun i => D.inflateNode hS (b.child i)), hcan, hpl, reconstruction_chainEmb D hS hd b,
      parAt_inflated D hS LG hd p _, ?_, rfl, fun z => rfl⟩
    exact layerAt_core D hS LG hd b

/-- **A layered garden decoded by `D` is determined by its core layering and its slot traces.** -/
theorem layered_eq_of_traces {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : D.Decodes hS LG'.garden) (hcore : coreLayer LG D hS hd = coreLayer LG' D hS hd')
    (htr : ∀ s, slotTrace D hS LG s = slotTrace D hS LG' s) : LG = LG' := by
  have hG : LG.garden = LG'.garden := (D.existsUnique_decodes hS).unique hd hd'
  rcases LG with ⟨G, l, hl⟩
  rcases LG' with ⟨G', l', hl'⟩
  dsimp only at hG hd hd' hcore htr
  subst G'
  have hlayers : l = l' := by
    funext z
    have key : layerAt ⟨G, l, hl⟩ z.1 = layerAt ⟨G, l', hl'⟩ z.1 := by
      rcases node_slot_cover D hS hd z with ⟨pr, h⟩ | ⟨b, h⟩ | ⟨b, h⟩
      · have := congrFun (htr (.inl pr)) z.1
        simpa only [slotTrace, if_pos h] using this
      · have := congrFun (htr (.inr b)) z.1
        simpa only [slotTrace, if_pos h] using this
      · rw [h, layerAt_core D hS _ hd, layerAt_core D hS _ hd', hcore]
    simpa only [layerAt_node] using key
  subst l'
  rfl

/-- **The number of layered gardens with a given core layering and slot incoherencies** is at most the product of
the `layerreg2` bounds (TARGET L2248-L2252). -/
theorem card_slot_bound (p : ℕ) (f : GBranch S.tree → ℕ) (gs : ReplacementSlot S → ℕ)
    (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ ∃ hd : D.Decodes hS LG.garden,
      coreLayer LG D hS hd = f ∧ ∀ s, slotInc D hS LG s = gs s) :
    A.card ≤ ∏ s, slotBound D hS p f (gs s) s := by
  classical
  let F : ∀ s : ReplacementSlot S, Finset (Fin w × Path → ℕ) := fun s =>
    (slotCarrier_finite D hS p f (gs s) s).toFinset
  have hmem : ∀ LG ∈ A, (fun s => slotTrace D hS LG s) ∈ Fintype.piFinset F := by
    intro LG hLG
    obtain ⟨hc, hp, hd, hcore, hinc⟩ := hA LG hLG
    rw [Fintype.mem_piFinset]
    intro s
    rw [Set.Finite.mem_toFinset]
    have := slotTrace_mem D hS hc hp hd s
    rw [hcore, hinc s] at this
    exact this
  have hinj : Set.InjOn (fun LG => fun s => slotTrace D hS LG s) (A : Set (LayeredGarden w)) := by
    intro LG hLG LG' hLG' he
    obtain ⟨-, -, hd, hcore, -⟩ := hA LG hLG
    obtain ⟨-, -, hd', hcore', -⟩ := hA LG' hLG'
    exact layered_eq_of_traces D hS hd hd' (hcore.trans hcore'.symm) (fun s => congrFun he s)
  calc A.card ≤ (Fintype.piFinset F).card := Finset.card_le_card_of_injOn _ hmem hinj
    _ = ∏ s, (F s).card := Fintype.card_piFinset F
    _ ≤ ∏ s, slotBound D hS p f (gs s) s := by
        refine Finset.prod_le_prod' fun s _ => ?_
        simp only [F]
        rw [← Set.ncard_eq_toFinset_card _ (slotCarrier_finite D hS p f (gs s) s)]
        exact slotCarrier_ncard_le D hS p f (gs s) s

end WaveTurbulence.GammaLow.Famc.ClassCount
