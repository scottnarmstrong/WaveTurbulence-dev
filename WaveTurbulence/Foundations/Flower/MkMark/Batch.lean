/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.MarkStep

/-! # B2b MK-MARK: Lemma 2⁺(a) for LF batches, coarse marking (milestone MK-α)

**Finding F-MK-1.** `MkDefs.MarkInvariantBatch` constrains only the family members that are vines of `𝒱`
(`mk A ⊆ vinesV`), while `CoreFamily` members need not be (e.g. the skipped top ingredient of an HVC). The corrected
batch statement `MarkInvariantBatchV` asks every family member to be the atom set of an unmarked vine of `𝒱`;
this is the form B4 uses (`A.state U` with `U ⊆ 𝒱`).

`markInvariantBatchV_markI0`: the coarse marking `markI0` is transported along every LF batch at unmarked `𝒱`
members (proved by induction on main's `BatchIso`, one LF operation at a time: `op_step`, from `mark_step`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- **Corrected Lemma 2⁺(a), batch form** (F-MK-1): every family member is an unmarked vine of `𝒱`. -/
def MarkInvariantBatchV (mk : MarkFn w) (Clean : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop) : Prop :=
  ∀ {p : ℕ} {kind : Bool} {ι : Type} {L : List ι} {A B : LFTwist.FamilyReconstruction w ι}
    (h : LFTwist.FamilyBatch p kind L A B) (hA : Reg.Skeleton.IsPrimeGarden A.skeleton),
    (∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧
      c ∉ mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)) →
    Clean (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) →
    MarkTransported (VineA.batchMolIso h)
      (mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered))
      (mk (⟨B.skeleton, VineA.batch_prime h hA, B.data, B.decodes⟩ : VineA.PrimeData B.layered))

/-! ## Composition -/

theorem transported_refl {S : Garden w} (M : Set (CLVine S)) : MarkTransported (VineA.molIsoRefl S) M M := by
  intro c c' h
  have e : c' = c := VineA.clVine_eq_of_atoms (h.trans Finset.image_id)
  rw [e]

theorem img_trans {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule) (G : MolIso S'.molecule S''.molecule)
    (U : Finset (GBranch S.tree)) : (VineA.molIsoTrans F G).img U = G.img (F.img U) := by
  unfold MolIso.img
  rw [Finset.image_image]
  rfl

theorem transported_trans {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (G : MolIso S'.molecule S''.molecule) {M : Set (CLVine S)} {M' : Set (CLVine S')} {M'' : Set (CLVine S'')}
    (hM : M ⊆ vinesV S) (hM'' : M'' ⊆ vinesV S'') (hF : MarkTransported F M M') (hG : MarkTransported G M' M'')
    (himF : ∀ c ∈ vinesV S, ∃ c' ∈ vinesV S', c'.atoms = F.img c.atoms)
    (hpreG : ∀ c'' ∈ vinesV S'', ∃ c' ∈ vinesV S', G.img c'.atoms = c''.atoms) :
    MarkTransported (VineA.molIsoTrans F G) M M'' := by
  intro c c'' hc''
  rw [img_trans] at hc''
  constructor
  · intro hc
    obtain ⟨c', -, hc'⟩ := himF c (hM hc)
    exact (hG c' c'' (by rw [hc'', hc'])).mp ((hF c c' hc').mp hc)
  · intro hc2
    obtain ⟨c', -, hc'⟩ := hpreG c'' (hM'' hc2)
    have ha : c'.atoms = F.img c.atoms := G.img_injective (hc'.trans hc'')
    exact (hF c c' ha).mpr ((hG c' c'' hc'.symm).mpr hc2)

/-! ## One operation -/

section Op
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)

/-- The coarse marked set of a family reconstruction. -/
def MV0 {ι : Type*} (A : FamilyReconstruction w ι) : Set (CLVine A.skeleton) :=
  markedVinesRaw A.skeleton A.data.tree (protI0 A.layered J pat t s)

/-- Every family member is an unmarked vine of `𝒱`. -/
def FamHyp {ι : Type*} (A : FamilyReconstruction w ι) : Prop :=
  ∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧ c ∉ MV0 J pat t s A

/-- The twist site of a family member that is a vine of `𝒱`. -/
def siteOf {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (c : CLVine A.skeleton) (hc : c ∈ vinesV A.skeleton)
    (he : c.atoms = A.family.atoms i) : TwistGroupSite A.skeleton where
  P := A.family.placement i
  S0 := A.family.atoms i
  a0 := A.family.upper i
  hB := (A.family.core i).1.1
  hCL := (A.family.core i).2.1
  hP := A.family.designated i
  Sg := hc.choose
  hSg := hc.choose_spec.1
  hS0 := he ▸ hc.choose_spec.2.1

theorem near_unmarked {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (c : CLVine A.skeleton)
    (hc : c ∈ vinesV A.skeleton) (he : c.atoms = A.family.atoms i) (hm : c ∉ MV0 J pat t s A) :
    ∀ a ∈ protI0 A.layered J pat t s, a.1 ∉ nearRegion A.skeleton A.data.tree (A.family.placement i).lower := by
  intro a ha hnear
  apply hm
  refine ⟨hc, (A.family.placement i).lower, ?_, ?_, a, ha, hnear⟩
  · rw [he]
    exact (A.family.core i).1.1.2.2.1
  · intro heq
    obtain ⟨h1, h2⟩ := (A.family.core i).2.1.2
    apply c.notParentUpper
    refine ⟨heq ▸ h1, ?_⟩
    rw [he]
    have e : GNode.parent c.upper.toNode (heq ▸ h1) = GNode.parent (A.family.placement i).lower.toNode h1 := by
      congr 1
      rw [heq]
    rw [e]
    exact h2

theorem vines_choice {S : Garden w} (Z : TwistGroupSite S) (ε : Bool) :
    (∀ c ∈ vinesV S, ∃ c' ∈ vinesV (chosenSkeleton S Z.P ε), c'.atoms = (VineA.chosenMolIso S Z.P ε).img c.atoms) ∧
    (∀ c' ∈ vinesV (chosenSkeleton S Z.P ε), ∃ c ∈ vinesV S, (VineA.chosenMolIso S Z.P ε).img c.atoms = c'.atoms) := by
  cases ε with
  | false => exact ⟨fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c' hc' => ⟨c', hc', Finset.image_id⟩⟩
  | true =>
    refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
    · obtain ⟨c', h1, h2, -⟩ := Z.vinesV_image hc
      exact ⟨c', h1, h2⟩
    · obtain ⟨c, h1, h2, -⟩ := Z.vinesV_preimage hc'
      exact ⟨c, h1, h2⟩

theorem nextFamily_atoms {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) (j : ι) :
    (A.nextFamily i ε).atoms j = (VineA.chosenMolIso A.skeleton (A.family.placement i) ε).img (A.family.atoms j) := by
  cases ε with
  | false => exact Finset.image_id.symm
  | true => rfl

variable {p : ℕ} {kind : Bool}

/-- **One LF operation at an unmarked `𝒱` member.** -/
theorem op_step {ι : Type*} {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (hF : FamHyp J pat t s A) :
    MarkTransported (VineA.operationMolIso op) (MV0 J pat t s A) (MV0 J pat t s op.output) ∧
      FamHyp J pat t s op.output ∧
      (∀ c ∈ vinesV A.skeleton, ∃ c' ∈ vinesV op.output.skeleton, c'.atoms = (VineA.operationMolIso op).img c.atoms) ∧
      (∀ c' ∈ vinesV op.output.skeleton, ∃ c ∈ vinesV A.skeleton, (VineA.operationMolIso op).img c.atoms = c'.atoms) := by
  obtain ⟨c, hc, he, hm⟩ := hF i
  let Z := siteOf A i c hc he
  have hdata : op.output.data = lfReconstructionChoice A.skeleton (A.family.placement i) A.plain A.data op.choice
      op.construction.newTree op.construction.newCouple op.construction.tree_wf op.construction.couple_wf :=
    (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).finalData_eq_choice op.choice _ _ _ _
  have hd' : (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
      op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).Decodes
      (chosenSkeleton_plain A.skeleton Z.P A.plain op.choice) op.output.layered.garden := by
    have := op.output.decodes
    rw [hdata] at this
    exact this
  have hmt := mark_step A.plain Z A.data op.construction.newTree op.construction.newCouple op.construction.tree_wf
    op.construction.couple_wf op.choice A.decodes hd' t s (near_unmarked J pat t s A i c hc he hm)
  have hMV : MV0 J pat t s op.output = markedVinesRaw (chosenSkeleton A.skeleton Z.P op.choice)
      (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
        op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree
      (protI0 op.output.layered J pat t s) := by
    unfold MV0
    rw [hdata]
    rfl
  have hT : MarkTransported (VineA.operationMolIso op) (MV0 J pat t s A) (MV0 J pat t s op.output) := by
    rw [hMV]
    exact hmt
  obtain ⟨him, hpre⟩ := vines_choice Z op.choice
  refine ⟨hT, ?_, him, hpre⟩
  intro j
  obtain ⟨cj, hcj, hej, hmj⟩ := hF j
  obtain ⟨cj', hcj', hej'⟩ := him cj hcj
  refine ⟨cj', hcj', ?_, fun h => hmj ((hT cj cj' hej').mpr h)⟩
  rw [hej', hej]
  exact (nextFamily_atoms A i op.choice j).symm

/-- **Lemma 2⁺(a), batch, coarse marking.** -/
theorem batch_mark {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamHyp J pat t s A →
      MarkTransported F (MV0 J pat t s A) (MV0 J pat t s B) ∧
      (∀ c ∈ vinesV A.skeleton, ∃ c' ∈ vinesV B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ vinesV B.skeleton, ∃ c ∈ vinesV A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _
    exact ⟨transported_refl _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF
    obtain ⟨h1, h2, h3, h4⟩ := op_step J pat t s op hF
    obtain ⟨g1, g3, g4⟩ := ih h2
    refine ⟨transported_trans _ _ (fun c hc => hc.1) (fun c hc => hc.1) h1 g1 h3 g4, ?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', e1⟩ := h3 c hc
      obtain ⟨c'', hc'', e2⟩ := g3 c' hc'
      exact ⟨c'', hc'', by rw [e2, e1, img_trans]⟩
    · intro c'' hc''
      obtain ⟨c', hc', e2⟩ := g4 c'' hc''
      obtain ⟨c, hc, e1⟩ := h4 c' hc'
      exact ⟨c, hc, by rw [img_trans, e1, e2]⟩

end Op

/-- **Milestone MK-α: the coarse marking `markI0` is invariant along LF batches at unmarked `𝒱` members.** -/
theorem markInvariantBatchV_markI0 (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) :
    MarkInvariantBatchV (markI0 J pat t s) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  exact (batch_mark J pat t s (VineA.batchMolIso_spec h) hfam).1

end WaveTurbulence.Flower.MkMark
