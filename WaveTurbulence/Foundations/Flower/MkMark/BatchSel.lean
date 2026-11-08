/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.MarkStepSel
public import WaveTurbulence.Foundations.Flower.MkMark.Batch

/-! # B2b-2 MK-MARK: Lemma 2⁺(a) for LF batches, fine marking `markI` (stem half)

The fine marking `markI J pat t s kSel` adds the selected capped-stem vertices to the seeds. It is transported along an
LF batch at unmarked `𝒱` members (F-MK-1 form) provided the capped stems avoid `𝐀(𝕍)` of every member `𝕍` of the
family (`StemCleanFam`, the family-relative stem-clean condition; StemZero's `StemCleanAt` for each member). Along the
batch the condition is carried in the weaker form `StemFam` (the capped stems avoid the replaced region of every
member's current placement), which one LF step transports (`lf_stemAvoid_next`, via `nextPlacement_lower/_retained`).

* `markInvariantBatchVF_markI : MarkInvariantBatchVF (markI J pat t s kSel) (fun A hA => StemCleanFam J A hA)`;
* `markInvariantBatchV_markI : MarkInvariantBatchV (markI J pat t s kSel) (StemCleanV J)`, with the
  family-independent `StemCleanV J A` (the capped stems avoid `𝐀(𝕍)` for every `𝕍 ∈ 𝒱`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-! ## Stem-avoidance of the next placements -/

section Next
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

include hsame in
/-- One LF step carries stem-avoidance of a placement's replaced nodes to the transported placement. -/
theorem lf_stemAvoid_next (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S P hS ε) LG'.garden)
    {J : Finset (Fin w)} (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes P)))
    (Pj : CorePlacement S) (Pj' : CorePlacement (chosenSkeleton S P ε))
    (e1 : Pj'.lower = chosenBranchEquiv S P ε Pj.lower) (e2 : Pj'.retained = chosenLeafEquiv S P ε Pj.retained)
    (hj : StemAvoid LG J (ownedBy S D.tree (replacedNodes Pj))) :
    StemAvoid LG' J (ownedBy (chosenSkeleton S P ε) (lfReconstructionChoice S P hS D ε X Q hX hQ).tree
      (replacedNodes Pj')) := by
  set C := lfCoord hS P D X Q hX hQ hsame ε
  have hs1 : StemAvoid LG J (ownedBy S D.tree C.Rsk) := by
    rw [lfCoord_rsk]
    exact hs
  obtain ⟨-, -, -, -, -, h6⟩ := C.stem_transport (lfPair hS P D X Q hX hQ hsame ε) hd hd'
    (lfCoord_root hS P D X Q hX hQ hsame ε) (lfCoord_pairR hS P D X Q hX hQ hsame ε)
    (lfCoord_root' hS P D X Q hX hQ hsame ε) (lfCoord_pairR' hS P D X Q hX hQ hsame ε) hs1
  exact h6 _ _ (fun o _ => lf_replaced_iff hS P D X Q hX hQ hsame ε Pj Pj' e1 e2 o) hj

end Next

theorem nextFamily_lower {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) (j : ι) :
    ((A.nextFamily i ε).placement j).lower =
      chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement j).lower := by
  cases ε
  · rfl
  · exact CoreFamily.nextPlacement_lower A.family i j

theorem nextFamily_retained {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) (j : ι) :
    ((A.nextFamily i ε).placement j).retained =
      chosenLeafEquiv A.skeleton (A.family.placement i) ε (A.family.placement j).retained := by
  cases ε
  · rfl
  · exact CoreFamily.nextPlacement_retained A.family i j

/-! ## One operation and the batch -/

section Op
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- The fine marked set of a family reconstruction. -/
def MVI {ι : Type*} (A : FamilyReconstruction w ι) : Set (CLVine A.skeleton) :=
  markedVinesRaw A.skeleton A.data.tree (protI A.layered J pat t s kSel)

/-- Every family member is a vine of `𝒱` unmarked for `Π`. -/
def FamHypI {ι : Type*} (A : FamilyReconstruction w ι) : Prop :=
  ∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧ c ∉ MVI J pat t s kSel A

/-- The capped stems avoid the replaced region of every member's placement. -/
def StemFam {ι : Type*} (A : FamilyReconstruction w ι) : Prop :=
  ∀ i, StemAvoid A.layered J (ownedBy A.skeleton A.data.tree (replacedNodes (A.family.placement i)))

theorem near_unmarkedI {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (c : CLVine A.skeleton)
    (hc : c ∈ vinesV A.skeleton) (he : c.atoms = A.family.atoms i) (hm : c ∉ MVI J pat t s kSel A) :
    ∀ a ∈ protI A.layered J pat t s kSel, a.1 ∉ nearRegion A.skeleton A.data.tree (A.family.placement i).lower := by
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

variable {p : ℕ} {kind : Bool}

/-- **One LF operation at an unmarked `𝒱` member, fine marking.** -/
theorem op_stepI {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) (hF : FamHypI J pat t s kSel A) (hst : StemFam J A) :
    MarkTransported (VineA.operationMolIso op) (MVI J pat t s kSel A) (MVI J pat t s kSel op.output) ∧
      FamHypI J pat t s kSel op.output ∧ StemFam J op.output ∧
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
  have hmt := mark_stepI A.plain Z A.data op.construction.newTree op.construction.newCouple op.construction.tree_wf
    op.construction.couple_wf op.choice A.decodes hd' t s kSel (near_unmarkedI J pat t s kSel A i c hc he hm) (hst i)
  have hMV : MVI J pat t s kSel op.output = markedVinesRaw (chosenSkeleton A.skeleton Z.P op.choice)
      (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
        op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree
      (protI op.output.layered J pat t s kSel) := by
    unfold MVI
    rw [hdata]
    rfl
  have hT : MarkTransported (VineA.operationMolIso op) (MVI J pat t s kSel A) (MVI J pat t s kSel op.output) := by
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
  obtain ⟨him, hpre⟩ := vines_choice Z op.choice
  refine ⟨hT, ?_, hSt, him, hpre⟩
  intro j
  obtain ⟨cj, hcj, hej, hmj⟩ := hF j
  obtain ⟨cj', hcj', hej'⟩ := him cj hcj
  refine ⟨cj', hcj', ?_, fun h => hmj ((hT cj cj' hej').mpr h)⟩
  rw [hej', hej]
  exact (nextFamily_atoms A i op.choice j).symm

/-- **Lemma 2⁺(a), batch, fine marking.** -/
theorem batch_markI {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamHypI J pat t s kSel A → StemFam J A →
      MarkTransported F (MVI J pat t s kSel A) (MVI J pat t s kSel B) ∧
      (∀ c ∈ vinesV A.skeleton, ∃ c' ∈ vinesV B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ vinesV B.skeleton, ∃ c ∈ vinesV A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _ _
    exact ⟨transported_refl _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF hst
    obtain ⟨h1, h2, h2', h3, h4⟩ := op_stepI J pat t s kSel op hF hst
    obtain ⟨g1, g3, g4⟩ := ih h2 h2'
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

/-! ## The statements -/

/-- **Lemma 2⁺(a), batch form, with a family-relative clean condition** (F-MK-1 member hypothesis). -/
def MarkInvariantBatchVF (mk : MarkFn w)
    (Clean : ∀ {ι : Type} (A : LFTwist.FamilyReconstruction w ι), Reg.Skeleton.IsPrimeGarden A.skeleton → Prop) :
    Prop :=
  ∀ {p : ℕ} {kind : Bool} {ι : Type} {L : List ι} {A B : LFTwist.FamilyReconstruction w ι}
    (h : LFTwist.FamilyBatch p kind L A B) (hA : Reg.Skeleton.IsPrimeGarden A.skeleton),
    (∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧
      c ∉ mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)) →
    Clean A hA →
    MarkTransported (VineA.batchMolIso h)
      (mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered))
      (mk (⟨B.skeleton, VineA.batch_prime h hA, B.data, B.decodes⟩ : VineA.PrimeData B.layered))

/-- **Family-relative stem cleanliness**: the capped stems avoid `𝐀(𝕍)` for every member `𝕍` of the family. -/
def StemCleanFam (J : Finset (Fin w)) {ι : Type} (A : LFTwist.FamilyReconstruction w ι)
    (hA : Reg.Skeleton.IsPrimeGarden A.skeleton) : Prop :=
  ∀ i, StemCleanAt J (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)
    (A.family.atoms i) (A.family.upper i)

/-- **Stem cleanliness for all of `𝒱`**: the capped stems avoid `𝐀(𝕍)` for every vine `𝕍 ∈ 𝒱`. -/
def StemCleanV (J : Finset (Fin w)) : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop :=
  fun A => ∀ c ∈ vinesV A.skeleton, StemCleanAt J A c.atoms c.upper

/-- `own(u₂) ∪ own(u₂₃) ∪ own(u₀) ⊆ 𝐀(U, u)` for any upper joint `u ≠ u₂` of a block with atoms `U`. -/
theorem replaced_sub_activeSet' {S : Garden w} (P : CorePlacement S) (X : GBranch S.tree → RegChain)
    {U : Finset (GBranch S.tree)} {a u : GBranch S.tree} (hB : S.molecule.IsBlock U a P.lower)
    (hP : IsPlacementAt S U P.lower P) (hne : P.lower ≠ u) :
    ownedBy S X (replacedNodes P) ⊆ activeSet S X U u := by
  have hpair := placement_pair_in_realization S P hB hP
  intro z hz
  have ho : owner S X z ∈ replacedNodes P := hz
  rw [mem_replacedNodes] at ho
  show owner S X z ∈ RegRed.clRealizationNodes S U ∧ owner S X z ≠ u.toNode
  rcases ho with h | h | h <;> rw [h]
  · exact ⟨mem_clRealizationNodes (Or.inl ⟨P.lower, hB.2.2.1, rfl⟩), fun e => hne (toNode_injective e)⟩
  · refine ⟨mem_clRealizationNodes ?_, leaf_ne_branch _ _⟩
    apply (Mole.leaf_incidence_realization_iff S U _).mpr
    exact (Mole.internal_leaf_pair_iff S U P.retained).mp ((Mole.leaf_incidence_realization_iff S U _).mp hpair)
  · exact ⟨mem_clRealizationNodes hpair, leaf_ne_branch _ _⟩

section Final
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- **Lemma 2⁺(a), batch, fine marking (stem half)**, family-relative stem cleanliness. -/
theorem markInvariantBatchVF_markI :
    MarkInvariantBatchVF (markI J pat t s kSel) (fun A hA => StemCleanFam J A hA) := by
  intro p kind ι L A B h hA hfam hcl
  refine (batch_markI J pat t s kSel (VineA.batchMolIso_spec h) hfam ?_).1
  intro i
  have h0 := (stemCleanAt_iff J _ _ _).mp (hcl i)
  exact stemAvoid_mono (replaced_sub_activeSet (A.family.placement i) A.data.tree (A.family.core i).1.1
    (A.family.core i).2.1 (A.family.designated i)) h0

/-- **Lemma 2⁺(a), batch, fine marking (stem half)** in the `MarkInvariantBatchV` form, with stem cleanliness for all
of `𝒱`. -/
theorem markInvariantBatchV_markI : MarkInvariantBatchV (markI J pat t s kSel) (StemCleanV J) := by
  intro p kind ι L A B h hA hfam hcl
  refine (batch_markI J pat t s kSel (VineA.batchMolIso_spec h) hfam ?_).1
  intro i
  obtain ⟨c, hc, he, -⟩ := hfam i
  have h0 := (stemCleanAt_iff J _ _ _).mp (hcl c hc)
  have hne : (A.family.placement i).lower ≠ c.upper := by
    intro heq
    obtain ⟨h1, h2⟩ := (A.family.core i).2.1.2
    apply c.notParentUpper
    refine ⟨heq ▸ h1, ?_⟩
    rw [he]
    have e : GNode.parent c.upper.toNode (heq ▸ h1) = GNode.parent (A.family.placement i).lower.toNode h1 := by
      congr 1
      rw [heq]
    rw [e]
    exact h2
  have hsub := replaced_sub_activeSet' (A.family.placement i) A.data.tree (A.family.core i).1.1
    (A.family.designated i) hne
  rw [← he] at hsub
  exact stemAvoid_mono hsub h0

end Final

end WaveTurbulence.Flower.MkMark
