/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMarkX.Defs
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderCore

/-! # B2e MK-X: the X transport (R177, F-B4-4 (b))

`markIX = markI ∪ X` is carried by every LF batch at unmarked `𝒱` members, from EVERY point.

* The member hypothesis `c ∉ markIX` gives `c ∉ markI` (B2b's `batch_markI` transports `markI`) and `c ∉ X`, i.e. every
  twisted member is stem-clean, so the capped stems avoid every member's replaced region (`StemFam`).
* **New content: `X` is transported.** One LF step (either choice) at a stem-clean member: B2b's
  `CoordData.stem_transport` (forward through the step's coordinate data, backward through `C.symm`) carries
  stem-avoidance of `ownedBy Q` to `ownedBy Q'` as soon as `ν o ∈ Q' ↔ o ∈ Q` off the replaced nodes. The twist-active
  set is `activeSet S X U u = ownedBy S X (activeNodes S U u)` with `activeNodes S U u = real(U) ∖ {u}`, and off the
  replaced nodes the naive node bijection `ν` of the unit twist carries `real(U)` to `real(twistedAtoms U)`
  (`twist_real_iff`: branches by `mem_twistedAtoms`, leaves by main's `ordinary_internal_iff`) and the upper joint of
  every `𝒱` vine to the upper joint of its image (`TwistGroupSite.vinesV_image`). So stem-cleanliness of EVERY vine of
  `𝒱` (twisted or not) is preserved (`stemClean_step`), and `X` is transported (`op_stepX`, `batch_markX`).

Exports: `markInvariantBatchV_markX`, `markInvariantBatchV_markIX`, `markInvariantBatchVF_markIX`,
`stage1Mk_markInvariantBatchV_markIX`, `fineTransportedAt_markIX`, `markI0_subset_markIX`, the `FineMarking` fields
`markI_subset_markIX`, `unclean_mem_markIX`, `markIX_le`, and the stem-free case `markI_eq_markI0_of_none`,
`fineTransportedAt_markI_of_none`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMarkX

variable {w : ℕ}

/-! ## The active set as an owned node set -/

/-- The skeleton nodes whose regions form `𝐀(U, u)`: the realization nodes other than the upper joint. -/
def activeNodes (S : Garden w) (U : Finset (GBranch S.tree)) (u : GBranch S.tree) : Set (GNode S.tree) :=
  {o | o ∈ RegRed.clRealizationNodes S U ∧ o ≠ u.toNode}

theorem activeSet_eq (S : Garden w) (X : GBranch S.tree → RegChain) (U : Finset (GBranch S.tree))
    (u : GBranch S.tree) : activeSet S X U u = ownedBy S X (activeNodes S U u) := rfl

/-! ## Realization nodes across a unit twist -/

/-- **Off the replaced nodes, the naive node bijection of a unit twist carries the realization of `U` onto the
realization of `twistedAtoms U`.** -/
theorem twist_real_iff {S : Garden w} (P : CorePlacement S) (U : Finset (GBranch S.tree)) (o : GNode S.tree)
    (ho : o ∉ replacedNodes P) :
    naiveNodeEquiv S P o ∈ RegRed.clRealizationNodes (unitTwistGarden S P) (twistedAtoms S P U) ↔
      o ∈ RegRed.clRealizationNodes S U := by
  rw [mem_replacedNodes, not_or, not_or] at ho
  obtain ⟨-, h2, h3⟩ := ho
  rcases (TTree.mem_nodes_iff _ _).mp o.2 with hl | hb
  · let l : GLeaf S.tree := ⟨o.1, hl⟩
    have hlo : l.toNode = o := rfl
    rw [← hlo, naiveNodeEquiv_leaf, RegRed.leaf_mem_clRealizationNodes (G := S)]
    refine (RegRed.leaf_mem_clRealizationNodes (G := unitTwistGarden S P) (U := twistedAtoms S P U)
      (coreLeafEquiv S P l)).trans (VineEstS4.ordinary_internal_iff S P l (fun e => h2 ?_) (fun e => h3 ?_))
    · rw [← hlo, e]
    · rw [← hlo, e]
  · let b : GBranch S.tree := ⟨o.1, hb⟩
    have hbo : b.toNode = o := rfl
    rw [← hbo, naiveNodeEquiv_branch, RegRed.branch_mem_clRealizationNodes (G := S)]
    exact (RegRed.branch_mem_clRealizationNodes (G := unitTwistGarden S P) (U := twistedAtoms S P U)
      (coreBranchEquiv S P b)).trans (mem_twistedAtoms S P U b)

/-! ## One LF step preserves stem-cleanliness of every vine of `𝒱` -/

section Step
variable {S : Garden w} (hS : S.IsPlain) (Z : TwistGroupSite S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- The active node sets of a `𝒱` vine and of its image correspond under the step's node map, off the replaced
nodes. -/
theorem activeNodes_step (hsame : (S.pair Z.P.retained).1.1 = Z.P.lower.1.1) (ε : Bool) (c : CLVine S)
    (hc : c ∈ vinesV S) (c' : CLVine (chosenSkeleton S Z.P ε))
    (hc' : c'.atoms = (VineA.chosenMolIso S Z.P ε).img c.atoms) (o : GNode S.tree) (ho : o ∉ replacedNodes Z.P) :
    (lfCoord hS Z.P D X Q hX hQ hsame ε).ν o ∈ activeNodes (chosenSkeleton S Z.P ε) c'.atoms c'.upper ↔
      o ∈ activeNodes S c.atoms c.upper := by
  cases ε with
  | false =>
    have hcc : c' = c := by
      apply VineA.clVine_eq_of_atoms
      rw [hc']
      exact Finset.image_id
    subst hcc
    exact Iff.rfl
  | true =>
    obtain ⟨c'', -, hc''a, hc''u, -⟩ := Z.vinesV_image hc
    have e : c'' = c' := VineA.clVine_eq_of_atoms (hc''a.trans hc'.symm)
    subst e
    show naiveNodeEquiv S Z.P o ∈ RegRed.clRealizationNodes (unitTwistGarden S Z.P) c''.atoms ∧
        naiveNodeEquiv S Z.P o ≠ c''.upper.toNode ↔ o ∈ RegRed.clRealizationNodes S c.atoms ∧ o ≠ c.upper.toNode
    have hu : c''.upper.toNode = naiveNodeEquiv S Z.P c.upper.toNode := by
      rw [hc''u]
      exact (naiveNodeEquiv_branch S Z.P c.upper).symm
    rw [hc''a, hu]
    exact and_congr (twist_real_iff Z.P c.atoms o ho) (not_congr (naiveNodeEquiv S Z.P).injective.eq_iff)

/-- **One LF step (either choice) at a member whose replaced region the capped stems avoid preserves the
stem-cleanliness of every vine of `𝒱`** (twisted or not), in both directions. -/
theorem stemClean_step (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} (hs : StemAvoid LG J (ownedBy S D.tree (replacedNodes Z.P)))
    (c : CLVine S) (hc : c ∈ vinesV S) (c' : CLVine (chosenSkeleton S Z.P ε))
    (hc' : c'.atoms = (VineA.chosenMolIso S Z.P ε).img c.atoms) :
    StemAvoid LG' J (activeSet (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        c'.atoms c'.upper) ↔ StemAvoid LG J (activeSet S D.tree c.atoms c.upper) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  set C := lfCoord hS Z.P D X Q hX hQ hsame ε
  set E := lfPair hS Z.P D X Q hX hQ hsame ε
  have hs1 : StemAvoid LG J (ownedBy S D.tree C.Rsk) := by
    rw [lfCoord_rsk]
    exact hs
  obtain ⟨-, -, -, -, h5, h6⟩ := C.stem_transport E hd hd' (lfCoord_root hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_pairR hS Z.P D X Q hX hQ hsame ε) (lfCoord_root' hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_pairR' hS Z.P D X Q hX hQ hsame ε) hs1
  obtain ⟨-, -, -, -, -, g6⟩ := C.symm.stem_transport E.symm hd' hd (lfCoord_root' hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_pairR' hS Z.P D X Q hX hQ hsame ε) (lfCoord_root hS Z.P D X Q hX hQ hsame ε)
    (lfCoord_pairR hS Z.P D X Q hX hQ hsame ε) h5
  have hAct : ∀ o, o ∉ C.Rsk → (C.ν o ∈ activeNodes (chosenSkeleton S Z.P ε) c'.atoms c'.upper ↔
      o ∈ activeNodes S c.atoms c.upper) := by
    intro o ho
    rw [lfCoord_rsk] at ho
    exact activeNodes_step hS Z D X Q hX hQ hsame ε c hc c' hc' o ho
  rw [activeSet_eq, activeSet_eq]
  constructor
  · intro h'
    refine g6 _ _ (fun o' ho' => ?_) h'
    have ho : C.ν.symm o' ∉ C.Rsk := fun h => ho' (by
      have := (C.rsk _).mpr h
      rwa [Equiv.apply_symm_apply] at this)
    have := hAct _ ho
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · exact h6 _ _ hAct

end Step

/-! ## One operation and the batch -/

section Op
variable (J : Finset (Fin w))

/-- The stem-unclean marked set of a family reconstruction. -/
def MX {ι : Type*} (A : FamilyReconstruction w ι) : Set (CLVine A.skeleton) :=
  {c | c ∈ vinesV A.skeleton ∧ ¬ StemAvoid A.layered J (activeSet A.skeleton A.data.tree c.atoms c.upper)}

/-- Every family member is (the atom set of) a vine of `𝒱`. -/
def FamV {ι : Type*} (A : FamilyReconstruction w ι) : Prop :=
  ∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i

variable {p : ℕ} {kind : Bool}

/-- **One LF operation at a `𝒱` member whose replaced region the capped stems avoid transports `X`.** -/
theorem op_stepX {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) (hF : FamV A) (hst : StemFam J A) :
    MarkTransported (VineA.operationMolIso op) (MX J A) (MX J op.output) ∧ FamV op.output ∧ StemFam J op.output ∧
      (∀ c ∈ vinesV A.skeleton, ∃ c' ∈ vinesV op.output.skeleton, c'.atoms = (VineA.operationMolIso op).img c.atoms) ∧
      (∀ c' ∈ vinesV op.output.skeleton, ∃ c ∈ vinesV A.skeleton, (VineA.operationMolIso op).img c.atoms = c'.atoms) := by
  obtain ⟨c, hc, he⟩ := hF i
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
  have hMX : MX J op.output = {c | c ∈ vinesV (chosenSkeleton A.skeleton Z.P op.choice) ∧
      ¬ StemAvoid op.output.layered J (activeSet (chosenSkeleton A.skeleton Z.P op.choice)
        (lfReconstructionChoice A.skeleton Z.P A.plain A.data op.choice op.construction.newTree
          op.construction.newCouple op.construction.tree_wf op.construction.couple_wf).tree c.atoms c.upper)} := by
    unfold MX
    rw [hdata]
    rfl
  obtain ⟨him, hpre⟩ := vines_choice Z op.choice
  have hT : MarkTransported (VineA.operationMolIso op) (MX J A) (MX J op.output) := by
    rw [hMX]
    intro c₁ c₁' hc₁'
    by_cases hv : c₁ ∈ vinesV A.skeleton
    · obtain ⟨c₂, hc₂V, hc₂a⟩ := him c₁ hv
      have e : c₂ = c₁' := VineA.clVine_eq_of_atoms (hc₂a.trans hc₁'.symm)
      subst e
      have hcl := stemClean_step A.plain Z A.data op.construction.newTree op.construction.newCouple
        op.construction.tree_wf op.construction.couple_wf op.choice A.decodes hd' (hst i) c₁ hv c₂ hc₁'
      exact ⟨fun ⟨_, hn⟩ => ⟨hc₂V, fun h => hn (hcl.mp h)⟩, fun ⟨_, hn⟩ => ⟨hv, fun h => hn (hcl.mpr h)⟩⟩
    · refine ⟨fun h => absurd h.1 hv, fun h => absurd ?_ hv⟩
      obtain ⟨c₀, hc₀V, hc₀a⟩ := hpre c₁' h.1
      have hae : c₀.atoms = c₁.atoms := (VineA.chosenMolIso A.skeleton Z.P op.choice).img_injective (hc₀a.trans hc₁')
      rw [← VineA.clVine_eq_of_atoms hae]
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

/-- **`X` along a batch at `𝒱` members whose replaced regions the capped stems avoid.** -/
theorem batch_markX {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : VineA.BatchIso p kind L A B F) :
    FamV A → StemFam J A →
      MarkTransported F (MX J A) (MX J B) ∧
      (∀ c ∈ vinesV A.skeleton, ∃ c' ∈ vinesV B.skeleton, c'.atoms = F.img c.atoms) ∧
      (∀ c' ∈ vinesV B.skeleton, ∃ c ∈ vinesV A.skeleton, F.img c.atoms = c'.atoms) := by
  induction h with
  | nil A =>
    intro _ _
    exact ⟨transported_refl _, fun c hc => ⟨c, hc, Finset.image_id.symm⟩, fun c hc => ⟨c, hc, Finset.image_id⟩⟩
  | skip i h ih => exact ih
  | apply op h ih =>
    intro hF hst
    obtain ⟨h1, h2, h2', h3, h4⟩ := op_stepX J op hF hst
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

/-! ## From the member hypothesis -/

theorem markX_eq_MX (J : Finset (Fin w)) {ι : Type} (A : FamilyReconstruction w ι)
    (hA : Reg.Skeleton.IsPrimeGarden A.skeleton) :
    markX J (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) = MX J A := by
  ext c
  exact and_congr Iff.rfl (not_congr (stemCleanAt_iff J _ _ _))

/-- A stem-clean member avoids its replaced region (the step in B2b's `markInvariantBatchV_markI`). -/
theorem stemFam_of_clean (J : Finset (Fin w)) {ι : Type} (A : FamilyReconstruction w ι)
    (hA : Reg.Skeleton.IsPrimeGarden A.skeleton)
    (h : ∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧
      StemCleanAt J (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) c.atoms c.upper) :
    StemFam J A := by
  intro i
  obtain ⟨c, -, he, hcl⟩ := h i
  have h0 := (stemCleanAt_iff J _ _ _).mp hcl
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

/-! ## The statements -/

section Final
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)

/-- **The X half alone**: the stem-unclean marking is carried by every LF batch at unmarked `𝒱` members. -/
theorem markInvariantBatchV_markX : MarkInvariantBatchV (markX J) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  have hF : FamV A := fun i => by
    obtain ⟨c, hc, he, -⟩ := hfam i
    exact ⟨c, hc, he⟩
  have hst : StemFam J A := stemFam_of_clean J A hA fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, by_contra fun hn => hm ⟨hc, hn⟩⟩
  have hX := (batch_markX J (VineA.batchMolIso_spec h) hF hst).1
  rw [← markX_eq_MX J A hA, ← markX_eq_MX J B (VineA.batch_prime h hA)] at hX
  exact hX

/-- **The X transport (R177, F-B4-4 (b)).** `markIX = markI ∪ X` is carried by every LF batch at unmarked `𝒱`
members, from every point. -/
theorem markInvariantBatchV_markIX : MarkInvariantBatchV (markIX J pat t s kSel) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  have hF : FamV A := fun i => by
    obtain ⟨c, hc, he, -⟩ := hfam i
    exact ⟨c, hc, he⟩
  have hst : StemFam J A := stemFam_of_clean J A hA fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, by_contra fun hn => hm (Or.inr ⟨hc, hn⟩)⟩
  have hFI : FamHypI J pat t s kSel A := fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, fun h' => hm (Or.inl h')⟩
  have hI := (batch_markI J pat t s kSel (VineA.batchMolIso_spec h) hFI hst).1
  have hX := (batch_markX J (VineA.batchMolIso_spec h) hF hst).1
  rw [← markX_eq_MX J A hA, ← markX_eq_MX J B (VineA.batch_prime h hA)] at hX
  intro c c' hc'
  exact or_congr (hI c c' hc') (hX c c' hc')

theorem markInvariantBatchVF_markIX : MarkInvariantBatchVF (markIX J pat t s kSel) (fun _ _ => True) :=
  fun h hA hfam _ => markInvariantBatchV_markIX J pat t s kSel h hA hfam trivial

/-- Main's form (`Stage1Mk.MarkInvariantBatchV`, the same body). -/
theorem stage1Mk_markInvariantBatchV_markIX :
    Stage1Mk.MarkInvariantBatchV (markIX J pat t s kSel) (fun _ => True) :=
  markInvariantBatchV_markIX J pat t s kSel

/-- **`FineMarking.fine` for `markIX`**: every fine′ batch from every prescribed point carries `markIX`. -/
theorem fineTransportedAt_markIX (a : VineA.PrescribedPrimeGarden w) : a.FineTransportedAt (markIX J pat t s kSel) :=
  VineA.PrescribedPrimeGarden.fineTransportedAt_of_markInvariantBatchV (Clean := fun _ => True)
    (stage1Mk_markInvariantBatchV_markIX J pat t s kSel) a trivial

/-! ### Inclusions -/

theorem protI0_subset_protI (LG : LayeredGarden w) : protI0 LG J pat t s ⊆ protI LG J pat t s kSel := by
  intro a ha
  obtain ⟨σ, hn, hσ⟩ := (mem_protI0_iff pat t s a).mp ha
  exact (mem_protI_iff pat t s kSel a).mpr ⟨a.2, σ, hn, Or.inl hσ⟩

/-- **`FineMarking.sub`.** -/
theorem markI_subset_markIX :
    ∀ {LG : LayeredGarden w} (B : VineA.PrimeData LG), markI J pat t s kSel B ⊆ markIX J pat t s kSel B := by
  intro LG B c hc
  exact Or.inl hc

/-- **`mkC ⊆ mkF`** (the `hsub` of main's `stage1Partition_prodMk`). -/
theorem markI0_subset_markIX {LG : LayeredGarden w} (B : VineA.PrimeData LG) :
    markI0 J pat t s B ⊆ markIX J pat t s kSel B := by
  rintro c ⟨hv, b, hb, hbu, a, ha, hn⟩
  exact Or.inl ⟨hv, b, hb, hbu, a, protI0_subset_protI J pat t s kSel LG ha, hn⟩

/-- **`FineMarking.stem`.** -/
theorem unclean_mem_markIX :
    ∀ {LG : LayeredGarden w} (B : VineA.PrimeData LG), ∀ c ∈ Stage1.vinesV B.skeleton,
      ¬ MkMark.StemCleanAt J B c.atoms c.upper → c ∈ markIX J pat t s kSel B := by
  intro LG B c hc hn
  exact Or.inr ⟨hc, hn⟩

/-- **`FineMarking.le`.** -/
theorem markIX_le :
    ∀ {LG : LayeredGarden w} (B : VineA.PrimeData LG), ∀ c ∈ markIX J pat t s kSel B,
      c ∈ markI J pat t s kSel B ∨ (c ∈ Stage1.vinesV B.skeleton ∧ ¬ MkMark.StemCleanAt J B c.atoms c.upper) := by
  intro LG B c hc
  exact hc

/-! ### The stem-free case: `markI` alone -/

theorem selSetCap_of_none (LG : LayeredGarden w) (hk : ∀ i, kSel i = none) : selSetCap LG J kSel = ∅ := by
  ext b
  simp [selSetCap, selCap, hk]

/-- With no depth selection, `markI = markI0`. -/
theorem markI_eq_markI0_of_none (hk : ∀ i, kSel i = none) {LG : LayeredGarden w} (B : VineA.PrimeData LG) :
    markI J pat t s kSel B = markI0 J pat t s B := by
  show markedVinesRaw B.skeleton B.data.tree (protI LG J pat t s kSel) =
    markedVinesRaw B.skeleton B.data.tree (protI0 LG J pat t s)
  unfold protI protI0
  rw [selSetCap_of_none J kSel LG hk]

/-- With no depth selection, `markI` alone is carried by every batch from every point (B2b's
`markInvariantBatchV_markI0`). -/
theorem stage1Mk_markInvariantBatchV_markI_of_none (hk : ∀ i, kSel i = none) :
    Stage1Mk.MarkInvariantBatchV (markI J pat t s kSel) (fun _ => True) := by
  intro p kind ι L A B h hA hfam _
  have eA := markI_eq_markI0_of_none J pat t s kSel hk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)
  have eB := markI_eq_markI0_of_none J pat t s kSel hk
    (⟨B.skeleton, VineA.batch_prime h hA, B.data, B.decodes⟩ : VineA.PrimeData B.layered)
  have h0 := markInvariantBatchV_markI0 J pat t s h hA (fun i => by
    obtain ⟨c, hc, he, hm⟩ := hfam i
    exact ⟨c, hc, he, fun h' => hm ((Set.ext_iff.mp eA c).mpr h')⟩) trivial
  intro c c' hc'
  exact (Set.ext_iff.mp eA c).trans ((h0 c c' hc').trans (Set.ext_iff.mp eB c').symm)

/-- **Stem-free `FineMarking.fine`**: with `kSel ≡ none`, `markI` is FineTransportedAt at every point. -/
theorem fineTransportedAt_markI_of_none (hk : ∀ i, kSel i = none) (a : VineA.PrescribedPrimeGarden w) :
    a.FineTransportedAt (markI J pat t s kSel) :=
  VineA.PrescribedPrimeGarden.fineTransportedAt_of_markInvariantBatchV (Clean := fun _ => True)
    (stage1Mk_markInvariantBatchV_markI_of_none J pat t s kSel hk) a trivial

end Final

end WaveTurbulence.Flower.MkMarkX
