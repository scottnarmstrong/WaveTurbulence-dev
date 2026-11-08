/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.ProtSel
public import WaveTurbulence.Foundations.Flower.MkMark.MarkStep

/-! # B2b-2 MK-MARK: one LF step transports the capped stem, the selected vertices and `Π`

* `CoordData.stem_transport`: coordinate data with slot data, whose replaced region the capped stems avoid, fix the
  capped stems; the two gardens have the same capped flowers, capped stems and depth-`k` stem vertices; the capped
  stems of the output avoid the image region, and stem-avoidance of any skeleton node set off `Rsk` is carried over.
* `CoordData.step_protSel`: the one-step transport of the fine protected set `Π`.
* `lfCoord`/`lfPair`: the coordinate and slot data of either LF choice (`idCoord` or `twistCoord`).
* `replaced_sub_activeSet`: the replaced region `own(u₂) ∪ own(u₂₃) ∪ own(u₀)` lies in `𝐀(𝕍)`;
  `stemCleanAt_iff`: `StemCleanAt` is `StemAvoid` of `𝐀(𝕍)`.
* **`lf_stem_transport`** (the export for CAPS-STABLE): if the capped stem avoids `𝐀(𝕍)` of the twisted member, one
  LF step (either choice) fixes the capped stem and carries over the capped flowers, the capped stems and their
  depth-`k` vertices (same addresses), and stem-avoidance of the replaced nodes of any other placement. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

theorem stemAvoid_mono {LG : LayeredGarden w} {J : Finset (Fin w)} {R₁ R₂ : Set (Address w)} (h : R₁ ⊆ R₂)
    (hs : StemAvoid LG J R₂) : StemAvoid LG J R₁ :=
  fun ℓ hℓ z hz hm => hs ℓ hℓ z hz (h hm)

/-- `StemCleanAt` (StemZero) is stem-avoidance of the twist-active set. -/
theorem stemCleanAt_iff {LG : LayeredGarden w} (J : Finset (Fin w)) (A : VineA.PrimeData LG)
    (U : Finset (GBranch A.skeleton.tree)) (u : GBranch A.skeleton.tree) :
    StemCleanAt J A U u ↔ StemAvoid LG J (activeSet A.skeleton A.data.tree U u) := by
  constructor
  · intro h ℓ hℓ z hz
    exact h ⟨z, nodeAt_of_addrBelow (nodeAt_of_leafAt hℓ.1) hz⟩ ((onCapStem_iff LG J _).mpr ⟨ℓ, hℓ, hz⟩)
  · intro h a ha
    obtain ⟨ℓ, hℓ, hz⟩ := (onCapStem_iff LG J a).mp ha
    exact h ℓ hℓ a.1 hz

/-! ## Coordinate data -/

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS') (E : PairData C)
  {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)

include E hd hd' in
/-- **Stem transport for coordinate data.** -/
theorem stem_transport {J : Finset (Fin w)}
    (hroot : ∀ o ∈ C.Rsk, o.1.2 ≠ []) (hpairR : ∀ l : GLeaf S.tree, l.toNode ∈ C.Rsk → (S.pair l).1.1 = l.1.1)
    (hroot' : ∀ o ∈ C.Rsk', o.1.2 ≠ [])
    (hpairR' : ∀ l : GLeaf S'.tree, l.toNode ∈ C.Rsk' → (S'.pair l).1.1 = l.1.1)
    (hs : StemAvoid LG J (ownedBy S D.tree C.Rsk)) :
    (∀ ℓ, CapFlowerAt LG' J ℓ ↔ CapFlowerAt LG J ℓ) ∧
      (∀ j z, CapStemAt LG' J j z ↔ CapStemAt LG J j z) ∧
      (∀ ℓ, CapFlowerAt LG J ℓ → ∀ z, AddrBelow z ℓ → z ∉ ownedBy S D.tree C.Rsk ∧ C.map z = z) ∧
      (∀ j k z, (∃ b, stemAt LG' J j k = some b ∧ b.1 = z) ↔ (∃ b, stemAt LG J j k = some b ∧ b.1 = z)) ∧
      StemAvoid LG' J (ownedBy S' D'.tree C.Rsk') ∧
      (∀ (Q : Set (GNode S.tree)) (Q' : Set (GNode S'.tree)), (∀ o, o ∉ C.Rsk → (C.ν o ∈ Q' ↔ o ∈ Q)) →
        StemAvoid LG J (ownedBy S D.tree Q) → StemAvoid LG' J (ownedBy S' D'.tree Q')) := by
  let I := C.toOutIso hd hd' (E.pairTree hd hd')
  let I' := C.symm.toOutIso hd' hd (E.symm.pairTree hd' hd)
  have hinv : ∀ z', NodeAt LG' z' → z' ∉ ownedBy S' D'.tree C.Rsk' → I.f (I'.f z') = z' :=
    fun z' hz' hR' => C.symm.symm_map_map hd' hd z' hz' hR'
  have hR := regionOK_ownedBy hd C.Rsk hroot hpairR
  have hR' := regionOK_ownedBy hd' C.Rsk' hroot' hpairR'
  obtain ⟨h1, h2, h3, h4⟩ := I.stem_transport I' hinv hR hR' hs
  refine ⟨h1, h2, h3, stemAt_congr h2, h4, ?_⟩
  intro Q Q' hQ hsQ ℓ' h z hz hm
  have hc := (h1 ℓ').mp h
  obtain ⟨hzR, e⟩ := h3 ℓ' hc z hz
  have hn := nodeAt_of_addrBelow (nodeAt_of_leafAt hc.1) hz
  have ho := (C.map_node hd hd' z hn hzR).2
  change owner S' D'.tree z ∈ Q' at hm
  have e' : C.map z = z := e
  rw [← e', ho] at hm
  exact hsQ ℓ' hc z hz ((hQ _ hzR).mp hm)

include E hd hd' in
/-- **One-step transport of `Π`** (fine protected set). -/
theorem step_protSel {J : Finset (Fin w)} {pat : Fin w → FixPat} (kSel : Fin w → Option ℕ)
    (hroot : ∀ o ∈ C.Rsk, o.1.2 ≠ []) (hpairR : ∀ l : GLeaf S.tree, l.toNode ∈ C.Rsk → (S.pair l).1.1 = l.1.1)
    (hroot' : ∀ o ∈ C.Rsk', o.1.2 ≠ [])
    (hpairR' : ∀ l : GLeaf S'.tree, l.toNode ∈ C.Rsk' → (S'.pair l).1.1 = l.1.1)
    (hp : ∀ z ∈ ownedBy S D.tree C.Rsk, ¬ ProtG LG (SeedSel LG J pat kSel) z)
    (hs : StemAvoid LG J (ownedBy S D.tree C.Rsk)) :
    (∀ z' ∈ ownedBy S' D'.tree C.Rsk', ¬ ProtG LG' (SeedSel LG' J pat kSel) z') ∧
      ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk →
        (ProtG LG' (SeedSel LG' J pat kSel) (C.map z) ↔ ProtG LG (SeedSel LG J pat kSel) z) := by
  let I := C.toOutIso hd hd' (E.pairTree hd hd')
  let I' := C.symm.toOutIso hd' hd (E.symm.pairTree hd' hd)
  have hinv : ∀ z', NodeAt LG' z' → z' ∉ ownedBy S' D'.tree C.Rsk' → I.f (I'.f z') = z' :=
    fun z' hz' hR' => C.symm.symm_map_map hd' hd z' hz' hR'
  have hinv' : ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk → I'.f (I.f z) = z :=
    fun z hz hR => C.symm_map_map hd hd' z hz hR
  obtain ⟨h1, h2, -⟩ := protSel_transport kSel I I' hinv hinv' (regionOK_ownedBy hd C.Rsk hroot hpairR)
    (regionOK_ownedBy hd' C.Rsk' hroot' hpairR') hp hs
  exact ⟨h1, h2⟩

end CoordData

/-! ## The two LF choices -/

section LF
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

/-- The coordinate data of either LF choice. -/
def lfCoord : (ε : Bool) →
    CoordData D hS (lfReconstructionChoice S P hS D ε X Q hX hQ) (chosenSkeleton_plain S P hS ε)
  | false => idCoord hS P D X Q hX hQ
  | true => twistCoord hS P D X Q hX hQ hsame

/-- The slot data of either LF choice. -/
def lfPair : (ε : Bool) → PairData (lfCoord hS P D X Q hX hQ hsame ε)
  | false => idPair hS P D X Q hX hQ
  | true => twistPair hS P D X Q hX hQ hsame

theorem lfCoord_rsk (ε : Bool) : (lfCoord hS P D X Q hX hQ hsame ε).Rsk = replacedNodes P := by
  cases ε <;> rfl

theorem lfPair_νB (ε : Bool) (b : GBranch S.tree) :
    (lfPair hS P D X Q hX hQ hsame ε).νB b = chosenBranchEquiv S P ε b := by
  cases ε <;> rfl

theorem lfPair_νL (ε : Bool) (l : GLeaf S.tree) :
    (lfPair hS P D X Q hX hQ hsame ε).νL l = chosenLeafEquiv S P ε l := by
  cases ε <;> rfl

theorem lfCoord_root (ε : Bool) : ∀ o ∈ (lfCoord hS P D X Q hX hQ hsame ε).Rsk, o.1.2 ≠ [] := by
  rw [lfCoord_rsk]
  exact replaced_nonroot P

theorem lfCoord_pairR (ε : Bool) :
    ∀ l : GLeaf S.tree, l.toNode ∈ (lfCoord hS P D X Q hX hQ hsame ε).Rsk → (S.pair l).1.1 = l.1.1 := by
  rw [lfCoord_rsk]
  exact replaced_pairTree P hsame

theorem lfCoord_root' (ε : Bool) : ∀ o ∈ (lfCoord hS P D X Q hX hQ hsame ε).Rsk', o.1.2 ≠ [] := by
  set C := lfCoord hS P D X Q hX hQ hsame ε
  intro o ho
  have h := lfCoord_root hS P D X Q hX hQ hsame ε (C.ν.symm o) ((C.rsk _).mp (by rw [Equiv.apply_symm_apply]; exact ho))
  exact fun h0 => h ((C.root (C.ν.symm o)).mp (by rw [Equiv.apply_symm_apply]; exact h0))

theorem lfCoord_pairR' (ε : Bool) : ∀ l' : GLeaf (chosenSkeleton S P ε).tree,
    l'.toNode ∈ (lfCoord hS P D X Q hX hQ hsame ε).Rsk' → ((chosenSkeleton S P ε).pair l').1.1 = l'.1.1 := by
  set C := lfCoord hS P D X Q hX hQ hsame ε
  set E := lfPair hS P D X Q hX hQ hsame ε
  intro l' hl'
  set l := E.νL.symm l'
  have e : l' = E.νL l := (Equiv.apply_symm_apply _ _).symm
  have hl : l.toNode ∈ C.Rsk := by
    apply (C.rsk _).mp
    rw [← E.hL, ← e]
    exact hl'
  have htree : ∀ x : GLeaf S.tree, (E.νL x).1.1 = x.1.1 := fun x => by
    have := C.tree x.toNode
    rw [← E.hL] at this
    exact this
  have hpr : (chosenSkeleton S P ε).pair (E.νL l) = E.νL (S.pair l) := by
    rw [lfPair_νL, lfPair_νL]
    exact (chosenLeafEquiv_pair S P ε l).symm
  rw [e, hpr, htree, htree]
  exact lfCoord_pairR hS P D X Q hX hQ hsame ε l hl

/-- Replaced nodes of a placement correspond to those of its transported placement. -/
theorem lf_replaced_iff (ε : Bool) (Pj : CorePlacement S) (Pj' : CorePlacement (chosenSkeleton S P ε))
    (h1 : Pj'.lower = chosenBranchEquiv S P ε Pj.lower) (h2 : Pj'.retained = chosenLeafEquiv S P ε Pj.retained)
    (o : GNode S.tree) :
    (lfCoord hS P D X Q hX hQ hsame ε).ν o ∈ replacedNodes Pj' ↔ o ∈ replacedNodes Pj := by
  set E := lfPair hS P D X Q hX hQ hsame ε
  rw [mem_replacedNodes, mem_replacedNodes, h1, h2, ← chosenLeafEquiv_pair, ← lfPair_νB hS P D X Q hX hQ hsame,
    ← lfPair_νL hS P D X Q hX hQ hsame, ← lfPair_νL hS P D X Q hX hQ hsame, E.hB, E.hL, E.hL]
  simp only [Equiv.apply_eq_iff_eq]

end LF

/-! ## The replaced region lies in the twist-active set -/

section Active
variable {S : Garden w} (P : CorePlacement S) {U : Finset (GBranch S.tree)} {u : GBranch S.tree}

theorem mem_clRealizationNodes {o : GNode S.tree} (h : Mole.InIncidenceRealization S U o) :
    o ∈ RegRed.clRealizationNodes S U := by
  unfold RegRed.clRealizationNodes
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- The replaced nodes `u₂, u₂₃, u₀` are realization nodes other than the upper joint. -/
theorem replaced_active (hB : S.molecule.IsBlock U u P.lower) (hCL : Mole.CLParentPattern S U u P.lower)
    (hP : IsPlacementAt S U P.lower P) :
    ∀ o ∈ replacedNodes P, o ∈ RegRed.clRealizationNodes S U ∧ o ≠ u.toNode := by
  have hpair := placement_pair_in_realization S P hB hP
  intro o ho
  rw [mem_replacedNodes] at ho
  rcases ho with rfl | rfl | rfl
  · refine ⟨mem_clRealizationNodes (Or.inl ⟨P.lower, hB.2.2.1, rfl⟩), fun h => ?_⟩
    have e : P.lower = u := toNode_injective h
    exact hCL.1 (e ▸ hCL.2)
  · refine ⟨mem_clRealizationNodes ?_, leaf_ne_branch _ _⟩
    apply (Mole.leaf_incidence_realization_iff S U _).mpr
    exact (Mole.internal_leaf_pair_iff S U P.retained).mp ((Mole.leaf_incidence_realization_iff S U _).mp hpair)
  · exact ⟨mem_clRealizationNodes hpair, leaf_ne_branch _ _⟩

/-- **`own(u₂) ∪ own(u₂₃) ∪ own(u₀) ⊆ 𝐀(𝕍)`.** -/
theorem replaced_sub_activeSet (X : GBranch S.tree → RegChain) (hB : S.molecule.IsBlock U u P.lower)
    (hCL : Mole.CLParentPattern S U u P.lower) (hP : IsPlacementAt S U P.lower P) :
    ownedBy S X (replacedNodes P) ⊆ activeSet S X U u :=
  fun _ hz => replaced_active P hB hCL hP _ hz

end Active

/-! ## The export: one LF step carries the capped stem over -/

section Export
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- **Stem transport along one LF step** (either choice `ε`; `𝕍 = (U, u)` the twisted member, `P` its designated
placement). If the capped stems of `LG` avoid `𝐀(𝕍)`, then the coordinate map of the step fixes every capped-stem
address (which lies off the replaced region), the output has the same capped flowers, the same capped stems (tree by
tree, as address sets, so with the same depths) and the same depth-`k` stem vertices as the input, its capped stems
avoid the image of the replaced region, and stem-avoidance of the replaced nodes of any other placement `Pj` is
carried over to its transported placement `Pj'`. -/
theorem lf_stem_transport (ε : Bool) {U : Finset (GBranch S.tree)} {u : GBranch S.tree}
    (hB : S.molecule.IsBlock U u P.lower) (hCL : Mole.CLParentPattern S U u P.lower)
    (hP : IsPlacementAt S U P.lower P) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S P hS ε) LG'.garden)
    {J : Finset (Fin w)} (hcl : StemAvoid LG J (activeSet S D.tree U u)) :
    (∀ ℓ, CapFlowerAt LG' J ℓ ↔ CapFlowerAt LG J ℓ) ∧
      (∀ j z, CapStemAt LG' J j z ↔ CapStemAt LG J j z) ∧
      (∀ ℓ, CapFlowerAt LG J ℓ → ∀ z, AddrBelow z ℓ → z ∉ ownedBy S D.tree (replacedNodes P) ∧
        (lfCoord hS P D X Q hX hQ (pair_retained_tree' P hB hCL hP) ε).map z = z) ∧
      (∀ j k z, (∃ b, stemAt LG' J j k = some b ∧ b.1 = z) ↔ (∃ b, stemAt LG J j k = some b ∧ b.1 = z)) ∧
      (∀ (Pj : CorePlacement S) (Pj' : CorePlacement (chosenSkeleton S P ε)),
        Pj'.lower = chosenBranchEquiv S P ε Pj.lower → Pj'.retained = chosenLeafEquiv S P ε Pj.retained →
        StemAvoid LG J (ownedBy S D.tree (replacedNodes Pj)) →
        StemAvoid LG' J (ownedBy (chosenSkeleton S P ε) (lfReconstructionChoice S P hS D ε X Q hX hQ).tree
          (replacedNodes Pj'))) := by
  have hsame := pair_retained_tree' P hB hCL hP
  set C := lfCoord hS P D X Q hX hQ hsame ε
  have hs : StemAvoid LG J (ownedBy S D.tree C.Rsk) := by
    rw [lfCoord_rsk]
    exact stemAvoid_mono (replaced_sub_activeSet P D.tree hB hCL hP) hcl
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := C.stem_transport (lfPair hS P D X Q hX hQ hsame ε) hd hd'
    (lfCoord_root hS P D X Q hX hQ hsame ε) (lfCoord_pairR hS P D X Q hX hQ hsame ε)
    (lfCoord_root' hS P D X Q hX hQ hsame ε) (lfCoord_pairR' hS P D X Q hX hQ hsame ε) hs
  refine ⟨h1, h2, ?_, h4, fun Pj Pj' e1 e2 => h6 _ _ fun o _ => lf_replaced_iff hS P D X Q hX hQ hsame ε Pj Pj' e1 e2 o⟩
  intro ℓ hℓ z hz
  have := h3 ℓ hℓ z hz
  rwa [lfCoord_rsk] at this

end Export

end WaveTurbulence.Flower.MkMark
