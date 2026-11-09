/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull
public import WaveTurbulence.Foundations.Flower.MkMark.Batch
public import WaveTurbulence.Foundations.Flower.MkMark.BatchSel
public import WaveTurbulence.Foundations.Flower.MkMark.CountBound
public import WaveTurbulence.Foundations.Flower.MkMarkX.Transport
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapJointChoice
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVCObjectGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedDesignatedSupport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I (wave 14): marked Stage-1′ declarations over `𝒱_γ`

Item-I declarations of L8's sub-areas (I-BASE, I-GATE) portable after L5a-G's `Vine.Align` publication, and
declarations deferred from earlier waves, copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkDefs
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Lemma 1⁺ (B2a target).** At most `3|Π|` vines of `𝒱` are marked. -/
def MarkCountBoundLow : Prop :=
  ∀ {w : ℕ} {LG : LayeredGarden w} (A : VineA.PrimeData LG) (Pi : Finset (GNode LG.garden.tree)),
    (markedVinesRawLow (γF := γF) A.skeleton A.data.tree Pi).ncard ≤ 3 * Pi.card

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
variable {p : ℕ} {kind : Bool}

/-- **One LF operation at an unmarked `𝒱` member.** -/
theorem op_stepLow {ι : Type*} {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (hF : FamHypLow (γF := γF) J pat t s A) :
    Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MV0Low (γF := γF) J pat t s A) (MV0Low (γF := γF) J pat t s op.output) ∧
      FamHypLow (γF := γF) J pat t s op.output ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF op.output.skeleton, c'.atoms = (VineA.operationMolIso op).img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF op.output.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, (VineA.operationMolIso op).img c.atoms = c'.atoms) := by
  obtain ⟨c, hc, he, hm⟩ := hF i
  let Z := siteOfLow A i c hc he
  have hdata : op.output.data = lfReconstructionChoice A.skeleton (A.family.placement i) A.plain A.data op.choice
      op.construction.newTree op.construction.newCouple op.construction.tree_wf op.construction.couple_wf :=
    (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).finalData_eq_choice op.choice _ _ _ _
  have hd' : (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
      op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).Decodes
      (chosenSkeleton_plain A.skeleton Z.P A.plain op.choice) op.output.layered.garden := by
    have := op.output.decodes
    rw [hdata] at this
    exact this
  have hmt := mark_stepLow A.plain Z A.data op.construction.newTree op.construction.newCouple op.construction.tree_wf
    op.construction.couple_wf op.choice A.decodes hd' t s (near_unmarkedLow J pat t s A i c hc he hm)
  have hMV : MV0Low (γF := γF) J pat t s op.output = markedVinesRawLow (γF := γF) (chosenSkeleton A.skeleton Z.P op.choice)
      (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
        op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree
      (protI0 op.output.layered J pat t s) := by
    unfold MV0Low
    rw [hdata]
    rfl
  have hT : Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MV0Low (γF := γF) J pat t s A) (MV0Low (γF := γF) J pat t s op.output) := by
    rw [hMV]
    exact hmt
  obtain ⟨him, hpre⟩ := vines_choiceLow Z op.choice
  refine ⟨hT, ?_, him, hpre⟩
  intro j
  obtain ⟨cj, hcj, hej, hmj⟩ := hF j
  obtain ⟨cj', hcj', hej'⟩ := him cj hcj
  refine ⟨cj', hcj', ?_, fun h => hmj ((hT cj cj' hej').mpr h)⟩
  rw [hej', hej]
  exact (nextFamily_atoms A i op.choice j).symm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
variable {p : ℕ} {kind : Bool}

/-- **Lemma 2⁺(a), batch, coarse marking.** -/
theorem batch_markLow {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamHypLow (γF := γF) J pat t s A →
      Fama.Stage1Mk.MarkTransported γF F (MV0Low (γF := γF) J pat t s A) (MV0Low (γF := γF) J pat t s B) ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF B.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _
    exact ⟨transported_reflLow _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF
    obtain ⟨h1, h2, h3, h4⟩ := op_stepLow J pat t s op hF
    obtain ⟨g1, g3, g4⟩ := ih h2
    refine ⟨transported_transLow _ _ (fun c hc => hc.1) (fun c hc => hc.1) h1 g1 h3 g4, ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', e1⟩ := h3 c hc
      obtain ⟨c'', hc'', e2⟩ := g3 c' hc'
      exact ⟨c'', hc'', by rw [e2, e1, img_trans]⟩
    · intro c'' hc''
      obtain ⟨c', hc', e2⟩ := g4 c'' hc''
      obtain ⟨c, hc, e1⟩ := h4 c' hc'
      exact ⟨c, hc, by rw [img_trans, e1, e2]⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Milestone MK-α: the coarse marking `markI0Low (γF := γF)` is invariant along LF batches at unmarked `𝒱` members.** -/
theorem markInvariantBatchV_markI0Low (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) :
    MarkInvariantBatchVLow (markI0Low (γF := γF) J pat t s) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  exact (batch_markLow J pat t s (VineA.batchMolIso_spec h) hfam).1

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
variable {p : ℕ} {kind : Bool}

/-- **One LF operation at an unmarked `𝒱` member, fine marking.** -/
theorem op_stepILow {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) (hF : FamHypILow (γF := γF) J pat t s kSel A) (hst : StemFam J A) :
    Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MVILow (γF := γF) J pat t s kSel A) (MVILow (γF := γF) J pat t s kSel op.output) ∧
      FamHypILow (γF := γF) J pat t s kSel op.output ∧ StemFam J op.output ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF op.output.skeleton, c'.atoms = (VineA.operationMolIso op).img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF op.output.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, (VineA.operationMolIso op).img c.atoms = c'.atoms) := by
  obtain ⟨c, hc, he, hm⟩ := hF i
  let Z := siteOfLow A i c hc he
  have hdata : op.output.data = lfReconstructionChoice A.skeleton (A.family.placement i) A.plain A.data op.choice
      op.construction.newTree op.construction.newCouple op.construction.tree_wf op.construction.couple_wf :=
    (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).finalData_eq_choice op.choice _ _ _ _
  have hd' : (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
      op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).Decodes
      (chosenSkeleton_plain A.skeleton Z.P A.plain op.choice) op.output.layered.garden := by
    have := op.output.decodes
    rw [hdata] at this
    exact this
  have hmt := mark_stepILow A.plain Z A.data op.construction.newTree op.construction.newCouple op.construction.tree_wf
    op.construction.couple_wf op.choice A.decodes hd' t s kSel (near_unmarkedILow J pat t s kSel A i c hc he hm) (hst i)
  have hMV : MVILow (γF := γF) J pat t s kSel op.output = markedVinesRawLow (γF := γF) (chosenSkeleton A.skeleton Z.P op.choice)
      (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
        op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree
      (protI op.output.layered J pat t s kSel) := by
    unfold MVILow
    rw [hdata]
    rfl
  have hT : Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MVILow (γF := γF) J pat t s kSel A) (MVILow (γF := γF) J pat t s kSel op.output) := by
    rw [hMV]
    exact hmt
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  have hSt : StemFam J op.output := by
    intro j
    have hj := lf_stemAvoid_next A.plain Z.P A.data op.construction.newTree op.construction.newCouple
      op.construction.tree_wf op.construction.couple_wf hsame op.choice A.decodes hd' (hst i) (A.family.placement j)
      ((A.nextFamily i op.choice).placement j) (nextFamily_lower A i op.choice j)
      (nextFamily_retained A i op.choice j) (hst j)
    show StemAvoid op.output.layered J (ownedBy (chosenSkeleton A.skeleton Z.P op.choice) op.output.data.tree
      (replacedNodes ((A.nextFamily i op.choice).placement j)))
    rw [hdata]
    exact hj
  obtain ⟨him, hpre⟩ := vines_choiceLow Z op.choice
  refine ⟨hT, ?_, hSt, him, hpre⟩
  intro j
  obtain ⟨cj, hcj, hej, hmj⟩ := hF j
  obtain ⟨cj', hcj', hej'⟩ := him cj hcj
  refine ⟨cj', hcj', ?_, fun h => hmj ((hT cj cj' hej').mpr h)⟩
  rw [hej', hej]
  exact (nextFamily_atoms A i op.choice j).symm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
variable {p : ℕ} {kind : Bool}

/-- **Lemma 2⁺(a), batch, fine marking.** -/
theorem batch_markILow {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamHypILow (γF := γF) J pat t s kSel A → StemFam J A →
      Fama.Stage1Mk.MarkTransported γF F (MVILow (γF := γF) J pat t s kSel A) (MVILow (γF := γF) J pat t s kSel B) ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF B.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _ _
    exact ⟨transported_reflLow _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF hst
    obtain ⟨h1, h2, h2', h3, h4⟩ := op_stepILow J pat t s kSel op hF hst
    obtain ⟨g1, g3, g4⟩ := ih h2 h2'
    refine ⟨transported_transLow _ _ (fun c hc => hc.1) (fun c hc => hc.1) h1 g1 h3 g4, ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', e1⟩ := h3 c hc
      obtain ⟨c'', hc'', e2⟩ := g3 c' hc'
      exact ⟨c'', hc'', by rw [e2, e1, img_trans]⟩
    · intro c'' hc''
      obtain ⟨c', hc', e2⟩ := g4 c'' hc''
      obtain ⟨c, hc, e1⟩ := h4 c' hc'
      exact ⟨c, hc, by rw [img_trans, e1, e2]⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Lemma 1⁺ (B2b target, o75 Lemma 1⁺).** At most `3|Π|` vines of `𝒱` are marked. -/
theorem markCountBoundLow : MarkCountBoundLow (γF := γF) := by
  intro w LG A Pi
  haveI : Fintype (Fama.CLVineG γF A.skeleton) := Fintype.ofFinite _
  let V : GBranch A.skeleton.tree → Finset (Fama.CLVineG γF A.skeleton) := fun b =>
    Finset.univ.filter fun c => c ∈ Fama.vinesVG γF A.skeleton ∧ b ∈ c.atoms ∧ b ≠ c.upper
  have hV : ∀ b, (V b).card ≤ 1 := by
    intro b
    refine Finset.card_le_one.mpr fun c hc c' hc' => ?_
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨h1', h2', h3'⟩ := (Finset.mem_filter.mp hc').2
    exact vinesV_eq_of_nonupperLow h1 h1' h2 h3 h2' h3'
  let U : Finset (Fama.CLVineG γF A.skeleton) :=
    Pi.biUnion fun a => (nearBranches A.skeleton A.data.tree a.1).biUnion V
  have hsub : markedVinesRawLow (γF := γF) A.skeleton A.data.tree Pi ⊆ (U : Set (Fama.CLVineG γF A.skeleton)) := by
    rintro c ⟨hc, b, hb, hbu, a, ha, hab⟩
    simp only [U, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exact ⟨a, ha, b, (mem_nearBranches _ _).mpr hab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hb, hbu⟩⟩
  have hU : ∀ a ∈ Pi, ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card ≤ 3 := by
    intro a _
    calc ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card
        ≤ ∑ b ∈ nearBranches A.skeleton A.data.tree a.1, (V b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ nearBranches A.skeleton A.data.tree a.1, 1 := Finset.sum_le_sum fun b _ => hV b
      _ = (nearBranches A.skeleton A.data.tree a.1).card := by simp
      _ ≤ 3 := card_nearBranches_le _ _ _
  calc (markedVinesRawLow (γF := γF) A.skeleton A.data.tree Pi).ncard ≤ (U : Set (Fama.CLVineG γF A.skeleton)).ncard :=
        Set.ncard_le_ncard hsub
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ ∑ a ∈ Pi, ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Pi, 3 := Finset.sum_le_sum hU
    _ = 3 * Pi.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w))
variable {p : ℕ} {kind : Bool}

/-- **One LF operation at a `𝒱` member whose replaced region the capped stems avoid transports `X`.** -/
theorem op_stepXLow {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) (hF : FamVLow (γF := γF) A) (hst : StemFam J A) :
    Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MXLow (γF := γF) J A) (MXLow (γF := γF) J op.output) ∧ FamVLow (γF := γF) op.output ∧ StemFam J op.output ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF op.output.skeleton, c'.atoms = (VineA.operationMolIso op).img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF op.output.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, (VineA.operationMolIso op).img c.atoms = c'.atoms) := by
  obtain ⟨c, hc, he⟩ := hF i
  let Z := siteOfLow A i c hc he
  have hdata : op.output.data = lfReconstructionChoice A.skeleton (A.family.placement i) A.plain A.data op.choice
      op.construction.newTree op.construction.newCouple op.construction.tree_wf op.construction.couple_wf :=
    (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).finalData_eq_choice op.choice _ _ _ _
  have hd' : (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
      op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).Decodes
      (chosenSkeleton_plain A.skeleton Z.P A.plain op.choice) op.output.layered.garden := by
    have := op.output.decodes
    rw [hdata] at this
    exact this
  have hMX : MXLow (γF := γF) J op.output = {c | c ∈ Fama.vinesVG γF (chosenSkeleton A.skeleton Z.P op.choice) ∧
      ¬ StemAvoid op.output.layered J (activeSet (chosenSkeleton A.skeleton Z.P op.choice)
        (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
          op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree c.atoms c.upper)} := by
    unfold MXLow
    rw [hdata]
    rfl
  obtain ⟨him, hpre⟩ := vines_choiceLow Z op.choice
  have hT : Fama.Stage1Mk.MarkTransported γF (VineA.operationMolIso op) (MXLow (γF := γF) J A) (MXLow (γF := γF) J op.output) := by
    rw [hMX]
    intro c₁ c₁' hc₁'
    by_cases hv : c₁ ∈ Fama.vinesVG γF A.skeleton
    · obtain ⟨c₂, hc₂V, hc₂a⟩ := him c₁ hv
      have e : c₂ = c₁' := Fama.VineA.clVine_eq_of_atoms (hc₂a.trans hc₁'.symm)
      subst e
      have hcl := stemClean_stepLow A.plain Z A.data op.construction.newTree op.construction.newCouple
        op.construction.tree_wf op.construction.couple_wf op.choice A.decodes hd' (hst i) c₁ hv c₂ hc₁'
      exact ⟨fun ⟨_, hn⟩ => ⟨hc₂V, fun h => hn (hcl.mp h)⟩, fun ⟨_, hn⟩ => ⟨hv, fun h => hn (hcl.mpr h)⟩⟩
    · refine ⟨fun h => absurd h.1 hv, fun h => absurd ?_ hv⟩
      obtain ⟨c₀, hc₀V, hc₀a⟩ := hpre c₁' h.1
      have hae : c₀.atoms = c₁.atoms := (VineA.chosenMolIso A.skeleton Z.P op.choice).img_injective (hc₀a.trans hc₁')
      rw [← Fama.VineA.clVine_eq_of_atoms hae]
      exact hc₀V
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  have hSt : StemFam J op.output := by
    intro j
    have hj := lf_stemAvoid_next A.plain Z.P A.data op.construction.newTree op.construction.newCouple
      op.construction.tree_wf op.construction.couple_wf hsame op.choice A.decodes hd' (hst i) (A.family.placement j)
      ((A.nextFamily i op.choice).placement j) (nextFamily_lower A i op.choice j)
      (nextFamily_retained A i op.choice j) (hst j)
    show StemAvoid op.output.layered J (ownedBy (chosenSkeleton A.skeleton Z.P op.choice) op.output.data.tree
      (replacedNodes ((A.nextFamily i op.choice).placement j)))
    rw [hdata]
    exact hj
  refine ⟨hT, ?_, hSt, him, hpre⟩
  intro j
  obtain ⟨cj, hcj, hej⟩ := hF j
  obtain ⟨cj', hcj', hej'⟩ := him cj hcj
  refine ⟨cj', hcj', ?_⟩
  rw [hej', hej]
  exact (nextFamily_atoms A i op.choice j).symm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w))
variable {p : ℕ} {kind : Bool}

/-- **`X` along a batch at `𝒱` members whose replaced regions the capped stems avoid.** -/
theorem batch_markXLow {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamVLow (γF := γF) A → StemFam J A →
      Fama.Stage1Mk.MarkTransported γF F (MXLow (γF := γF) J A) (MXLow (γF := γF) J B) ∧
      (∀ c ∈ Fama.vinesVG γF A.skeleton, ∃ c' ∈ Fama.vinesVG γF B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ Fama.vinesVG γF B.skeleton, ∃ c ∈ Fama.vinesVG γF A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _ _
    exact ⟨transported_reflLow _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF hst
    obtain ⟨h1, h2, h2', h3, h4⟩ := op_stepXLow J op hF hst
    obtain ⟨g1, g3, g4⟩ := ih h2 h2'
    refine ⟨transported_transLow _ _ (fun c hc => hc.1) (fun c hc => hc.1) h1 g1 h3 g4, ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', e1⟩ := h3 c hc
      obtain ⟨c'', hc'', e2⟩ := g3 c' hc'
      exact ⟨c'', hc'', by rw [e2, e1, img_trans]⟩
    · intro c'' hc''
      obtain ⟨c', hc', e2⟩ := g4 c'' hc''
      obtain ⟨c, hc, e1⟩ := h4 c' hc'
      exact ⟨c, hc, by rw [img_trans, e1, e2]⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- **The X half alone**: the stem-unclean marking is carried by every LF batch at unmarked `𝒱` members. -/
theorem markInvariantBatchV_markXLow : MarkInvariantBatchVLow (markXLow (γF := γF) J) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  have hF : FamVLow (γF := γF) A := fun i => by
    obtain ⟨c, hc, he, -⟩ := hfam i
    exact ⟨c, hc, he⟩
  have hst : StemFam J A := stemFam_of_cleanLow J A hA fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, by_contra fun hn => hm ⟨hc, hn⟩⟩
  have hX := (batch_markXLow J (VineA.batchMolIso_spec h) hF hst).1
  rw [← markX_eq_MXLow J A hA, ← markX_eq_MXLow J B (VineA.batch_prime h hA)] at hX
  exact hX

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- **The X transport (R177, F-B4-4 (b)).** `markIXLow (γF := γF) = markILow (γF := γF) ∪ X` is carried by every LF batch at unmarked `𝒱`
members, from every point. -/
theorem markInvariantBatchV_markIXLow : MarkInvariantBatchVLow (markIXLow (γF := γF) J pat t s kSel) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  have hF : FamVLow (γF := γF) A := fun i => by
    obtain ⟨c, hc, he, -⟩ := hfam i
    exact ⟨c, hc, he⟩
  have hst : StemFam J A := stemFam_of_cleanLow J A hA fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, by_contra fun hn => hm (Or.inr ⟨hc, hn⟩)⟩
  have hFI : FamHypILow (γF := γF) J pat t s kSel A := fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, fun h' => hm (Or.inl h')⟩
  have hI := (batch_markILow J pat t s kSel (VineA.batchMolIso_spec h) hFI hst).1
  have hX := (batch_markXLow J (VineA.batchMolIso_spec h) hF hst).1
  rw [← markX_eq_MXLow J A hA, ← markX_eq_MXLow J B (VineA.batch_prime h hA)] at hX
  intro c c' hc'
  exact or_congr (hI c c' hc') (hX c c' hc')

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- Main's form (`Fama.Stage1Mk.MarkInvariantBatchV γF`, the same body). -/
theorem stage1Mk_markInvariantBatchV_markIXLow :
    Fama.Stage1Mk.MarkInvariantBatchV γF (markIXLow (γF := γF) J pat t s kSel) (fun _ => True) :=
  markInvariantBatchV_markIXLow J pat t s kSel

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **The gap kind of an ingredient pair** (o75 Lemma 3: survivors carry the gap of their chain; R171).  An out/in pair
of darts inside an ingredient `T` of the group `S`, at a joint of `T`, has the gap kind of the designated object of
`S`. -/
theorem ingredient_pair_gapKindLow (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hI : Fama.IsIngredientG γF G.molecule S T)
    {j l : GBranch G.tree} (hT : Src.IsSomeVine γF G.molecule T j l) {p : GardenDart G × GardenDart G}
    (hp : SurvPairSpec G T j p) {P : Src.Object γF G.molecule} (hP : Fama.VineA.NormalizedSplice.designatedObject γF G S = some P)
    {k : Molecule.GapKind} (hk : P.HasGapKind L γ η w κ k) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
  obtain ⟨hk1, hc1⟩ := RedSplice.kvec_cons L w c κ hκ hc0
  obtain ⟨⟨hpx, hpy, -, hne⟩, hgx, hgy⟩ := hp
  have hX := hT
  unfold Molecule.gapAt
  rcases hI with ⟨a, b, n, x0, y0, hU, hCI⟩ | ⟨a, b, e, n, x0, y0, hends, hn2, hUN, hCI⟩
  · -- a VC group
    obtain ⟨hchain, hX0, -⟩ := Fama.chainIngredientG_spec hCI
    have hj : j = x0 ∨ j = y0 := by
      have hu := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hX) (Src.isBlock_of_isSomeVine hX0)
      have : j ∈ ({x0, y0} : Finset _) := by rw [← hu]; simp
      simpa using this
    have hn := Fama.pair_norm_ingredient G.molecule hM hCI hU hj (Molecule.kvec L w κ) hk1 hc1 hpx hpy hgx hgy hne
    have hVC : Src.IsVC γF G.molecule S a b := ⟨hU, n, id hchain⟩
    obtain ⟨P', hP', hPa, hPt⟩ := Fama.VineA.NormalizedSplice.designatedObject_ordinary hS hVC
    rw [hP] at hP'
    cases hP'
    let OS : Src.Object γF G.molecule := ⟨S, a, b, .vc hVC⟩
    have hOS : OS.HasGapKind L γ η w κ k :=
      (Fama.VineA.ordinary_objects_gapKind_iff hM OS P hPa.symm rfl hPt L γ η w c κ hκ hc0 k).mpr hk
    obtain ⟨r, hr, rfl⟩ := hOS
    exact kind_of_flow_norm G.molecule hU L γ η w κ hr hn
  · -- an HVC group: the chain lives in the adjoint `eraseBond`
    obtain ⟨hchain, hX0, -⟩ := Fama.chainIngredientG_spec hCI
    have hnot : ¬ (a ∈ T ∧ b ∈ T) := chainIngredient_not_bothLow hCI hn2
    have hX0M : G.molecule.IsBlock T x0 y0 := (block_transfer G.molecule hends hnot x0 y0).mp (Src.isBlock_of_isSomeVine hX0)
    have hj : j = x0 ∨ j = y0 := by
      have hu := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hX) hX0M
      have : j ∈ ({x0, y0} : Finset _) := by rw [← hu]; simp
      simpa using this
    have hab : a ≠ b := hUN.2.2.2.1
    have hne' := Vine.ends_distinct_of_pair G.molecule e hends hab
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne'
    obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists G.molecule hM e hne' L w c κ hκ hc0
    obtain ⟨hk2, hc2⟩ := RedSplice.kvec_cons L w cN (fun z => κ z.1) hκN hcN
    -- the darts of the pair avoid the added bond: its ends are the outer joints `a, b`
    have hendsat : G.molecule.ends e = s(G.molecule.atom e, G.molecule.atom (G.molecule.mate e)) := rfl
    have havoid : ∀ z : GardenDart G, G.molecule.InGroup T z → z ≠ e ∧ z ≠ G.molecule.mate e := by
      intro z hz
      have hab' : ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) = {a, b} := by
        rw [hendsat] at hends
        rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Finset.pair_comm]
      have hboth : G.molecule.atom e ∈ T ∧ G.molecule.atom (G.molecule.mate e) ∈ T → False := by
        intro ⟨h1, h2⟩
        apply hnot
        have ha : a ∈ ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) := by
          rw [hab']; simp
        have hb : b ∈ ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) := by
          rw [hab']; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        constructor
        · rcases ha with rfl | rfl <;> assumption
        · rcases hb with rfl | rfl <;> assumption
      refine ⟨fun hze => hboth ?_, fun hze => hboth ?_⟩
      · subst hze; exact ⟨hz.1, hz.2⟩
      · subst hze
        refine ⟨?_, hz.1⟩
        have := hz.2
        rwa [G.molecule.mate_mate] at this
    obtain ⟨he1, he2⟩ := havoid p.1 hgx
    obtain ⟨he3, he4⟩ := havoid p.2 hgy
    have hn := Fama.pair_norm_ingredient (eraseBond G.molecule e) hN hCI hUN hj (Molecule.kvec L w (fun z => κ z.1))
      hk2 hc2 (x := ⟨p.1, he1, he2⟩) (y := ⟨p.2, he3, he4⟩) hpx hpy hgx hgy hne
    have hHVC : Src.IsHVC γF G.molecule S a b := ⟨e, hends, hUN, n, hn2, id hchain⟩
    obtain ⟨P', hP', hPa⟩ := Fama.VineA.NormalizedSplice.designatedObject_atoms hS ⟨a, b, Or.inr (Or.inr hHVC)⟩
    rw [hP] at hP'
    cases hP'
    let OS : Src.Object γF G.molecule := ⟨S, a, b, .hyper ⟨e, hends, ⟨hUN, n, id hchain⟩⟩⟩
    have hOS : OS.HasGapKind L γ η w κ k :=
      (Fama.VineA.objects_gapKind_iff_of_HVC hM OS P hPa.symm hHVC L γ η w c κ hκ hc0 k).mpr hk
    obtain ⟨r, hr, rfl⟩ := hOS
    unfold Src.VineLikeObject.IsGap at hr
    exact kind_of_flow_norm (eraseBond G.molecule e) hUN L γ η w (fun z => κ z.1) hr hn

end

end WaveTurbulence.GammaLow.Flower
