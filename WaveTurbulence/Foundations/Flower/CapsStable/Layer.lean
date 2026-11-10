/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Geo
public import WaveTurbulence.Foundations.Flower.MkMark.IdStep
public import WaveTurbulence.Foundations.Molecule.LFTwist.NativeCoordinateEquiv
public import WaveTurbulence.Foundations.Molecule.LFTwist.LFReinsertData

/-! # CAPS-STABLE: one LF operation is a layered correspondence off the replaced region

For an LF construction `h : LFConstruction s ε` the skeleton coordinates of B2b (`idCoord`/`twistCoord`, here
`choiceCoord`) give a correspondence `C.map` of the source garden and the output off the replaced region
`R = own(u₂) ∪ own(u₂₃) ∪ own(u₀)`. This file adds the **layer transport** (`layer_map`): a node off `R` is owned by a
branch `b ≠ u₂` (its regular tree is kept with its layers, `LFConstruction.ordinaryTreeLayers`) or by a leaf of an
ordinary pair (its couple is kept with its layers, `LFConstruction.ordinaryCoupleLayers`). Bundled: `stepIso`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

/-! ## The coordinate data of either choice -/

section Choice
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

/-- B2b's coordinate data of the LF choice `ε` (identity for `false`, the unit twist for `true`). -/
def choiceCoord : ∀ ε : Bool,
    CoordData D hS (lfReconstructionChoice S P hS D ε X Q hX hQ) (chosenSkeleton_plain S P hS ε)
  | false => idCoord hS P D X Q hX hQ
  | true => twistCoord hS P D X Q hX hQ hsame

/-- B2b's slot data of the LF choice `ε`. -/
def choicePair : ∀ ε : Bool, PairData (choiceCoord hS P D X Q hX hQ hsame ε)
  | false => idPair hS P D X Q hX hQ
  | true => twistPair hS P D X Q hX hQ hsame

theorem choiceCoord_rsk (ε : Bool) : (choiceCoord hS P D X Q hX hQ hsame ε).Rsk = replacedNodes P := by
  cases ε <;> rfl

theorem choicePair_νB (ε : Bool) (b : GBranch S.tree) :
    (choicePair hS P D X Q hX hQ hsame ε).νB b = chosenBranchEquiv S P ε b := by
  cases ε <;> rfl

theorem choicePair_νL (ε : Bool) (l : GLeaf S.tree) :
    (choicePair hS P D X Q hX hQ hsame ε).νL l = chosenLeafEquiv S P ε l := by
  cases ε <;> rfl

theorem choice_rootR' (ε : Bool) : ∀ o ∈ (choiceCoord hS P D X Q hX hQ hsame ε).Rsk', o.1.2 ≠ [] := by
  set C := choiceCoord hS P D X Q hX hQ hsame ε
  intro o ho h0
  have ho' : C.ν.symm o ∈ C.Rsk := by rw [← C.rsk, Equiv.apply_symm_apply]; exact ho
  rw [choiceCoord_rsk] at ho'
  exact replaced_nonroot P _ ho' ((C.root (C.ν.symm o)).mp (by rw [Equiv.apply_symm_apply]; exact h0))

theorem choice_pairR' (ε : Bool) :
    ∀ l' : GLeaf (chosenSkeleton S P ε).tree, l'.toNode ∈ (choiceCoord hS P D X Q hX hQ hsame ε).Rsk' →
      ((chosenSkeleton S P ε).pair l').1.1 = l'.1.1 := by
  set C := choiceCoord hS P D X Q hX hQ hsame ε
  set E := choicePair hS P D X Q hX hQ hsame ε
  intro l' hl'
  set l := E.νL.symm l'
  have hl : l.toNode ∈ replacedNodes P := by
    have : C.ν.symm l'.toNode ∈ C.Rsk := by rw [← C.rsk, Equiv.apply_symm_apply]; exact hl'
    rw [choiceCoord_rsk] at this
    rwa [show C.ν.symm l'.toNode = l.toNode by
      apply C.ν.injective
      rw [Equiv.apply_symm_apply, ← E.hL, Equiv.apply_symm_apply]] at this
  have e : l' = E.νL l := (Equiv.apply_symm_apply _ _).symm
  have hpr : (chosenSkeleton S P ε).pair (E.νL l) = E.νL (S.pair l) := by
    rw [choicePair_νL, choicePair_νL]
    exact (chosenLeafEquiv_pair S P ε l).symm
  have htree : ∀ x : GLeaf S.tree, (E.νL x).1.1 = x.1.1 := fun x => by
    have := C.tree x.toNode
    rw [← E.hL] at this
    exact this
  rw [e, hpr, htree, htree]
  exact replaced_pairTree P hsame l hl

end Choice

/-! ## The layer transport -/

section Layer
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) {ε : Bool}
  (h : LFConstruction s ε)

/-- **Layers off the replaced region are kept.** -/
theorem layer_map {D' : ReconstructionData (s.chosen ε)} (hD' : D' = h.data)
    (C : CoordData s.data s.plain D' (s.chosen_plain ε)) (E : PairData C)
    (hRsk : C.Rsk = replacedNodes s.placement) (hνB : ∀ b, E.νB b = s.branches ε b)
    (hνL : ∀ l, E.νL l = chosenLeafEquiv s.skeleton s.placement ε l)
    (z : Address w) (hz : NodeAt LG z) (hR : z ∉ ownedBy s.skeleton s.data.tree C.Rsk) :
    layerAt h.output (C.map z) = layerAt LG z := by
  subst hD'
  have ho : owner s.skeleton s.data.tree z ∉ replacedNodes s.placement := by rw [← hRsk]; exact hR
  have hzq := coord_eq s.skeleton s.data.tree z
  have hq := node_local s.data s.plain s.decodes z hz
  have hmap : C.map z = addrExt (inflatedPosition (s.chosen ε) h.data.tree (C.ν (owner s.skeleton s.data.tree z)))
      (localPath s.skeleton s.data.tree z) := rfl
  rcases (TTree.mem_nodes_iff _ _).mp (owner s.skeleton s.data.tree z).2 with hl | hb
  · -- a leaf of an ordinary pair
    let l : GLeaf s.skeleton.tree := ⟨(owner s.skeleton s.data.tree z).1, hl⟩
    have hlo : l.toNode = owner s.skeleton s.data.tree z := rfl
    have hl1 : l ≠ s.placement.retained := fun e => ho (by
      rw [← hlo, e]; exact (mem_replacedNodes _ _).mpr (Or.inr (Or.inl rfl)))
    have hl2 : l ≠ s.skeleton.pair s.placement.retained := fun e => ho (by
      rw [← hlo, e]; exact (mem_replacedNodes _ _).mpr (Or.inr (Or.inr rfl)))
    have hq' : pairOfLeaf s.skeleton s.plain l ≠ s.exceptional := fun he => by
      rcases VineAlign.pairOfLeaf_eq_cases s.plain l s.placement.retained he with e | e
      exacts [hl1 e, hl2 e]
    rw [← hlo, localTree_leaf] at hq
    unfold ReconstructionData.leafTree treeOfSign at hq
    have hν : C.ν (owner s.skeleton s.data.tree z) = (chosenLeafEquiv s.skeleton s.placement ε l).toNode := by
      rw [← hlo, ← E.hL]; exact congrArg GLeaf.toNode (hνL l)
    have hzl : z = addrExt (inflatedPosition s.skeleton s.data.tree l.toNode) (localPath s.skeleton s.data.tree z) :=
      hzq
    by_cases hs : nodeSign s.skeleton.sig l.1 = 1
    · obtain ⟨hf, -⟩ := pairOfLeaf_sides_pos s.skeleton s.plain l hs
      rw [ite_eq_left hs] at hq
      have key : layerAt LG (addrExt (coupleRoot s.data s.plain (pairOfLeaf s.skeleton s.plain l) 0)
            (localPath s.skeleton s.data.tree z)) =
          layerAt h.output (addrExt (coupleRoot h.data (s.chosen_plain ε)
            (s.pairs ε (pairOfLeaf s.skeleton s.plain l)) 0) (localPath s.skeleton s.data.tree z)) :=
        h.ordinaryCoupleLayers _ hq' 0 _ hq
      have hc : coupleRoot s.data s.plain (pairOfLeaf s.skeleton s.plain l) 0 =
          inflatedPosition s.skeleton s.data.tree l.toNode := by
        unfold coupleRoot; rw [ite_eq_left rfl, hf]
      have hc' : coupleRoot h.data (s.chosen_plain ε) (s.pairs ε (pairOfLeaf s.skeleton s.plain l)) 0 =
          inflatedPosition (s.chosen ε) h.data.tree (chosenLeafEquiv s.skeleton s.placement ε l).toNode := by
        unfold coupleRoot; rw [ite_eq_left rfl, (s.ordinary_pair_sides ε _ hq').1, hf]; rfl
      rw [hc, hc'] at key
      rw [hmap, hν, ← key, ← hzl]
    · obtain ⟨-, hf⟩ := pairOfLeaf_sides_neg s.skeleton s.plain l hs
      rw [ite_eq_right hs] at hq
      have key : layerAt LG (addrExt (coupleRoot s.data s.plain (pairOfLeaf s.skeleton s.plain l) 1)
            (localPath s.skeleton s.data.tree z)) =
          layerAt h.output (addrExt (coupleRoot h.data (s.chosen_plain ε)
            (s.pairs ε (pairOfLeaf s.skeleton s.plain l)) 1) (localPath s.skeleton s.data.tree z)) :=
        h.ordinaryCoupleLayers _ hq' 1 _ hq
      have hc : coupleRoot s.data s.plain (pairOfLeaf s.skeleton s.plain l) 1 =
          inflatedPosition s.skeleton s.data.tree l.toNode := by
        unfold coupleRoot; rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), hf]
      have hc' : coupleRoot h.data (s.chosen_plain ε) (s.pairs ε (pairOfLeaf s.skeleton s.plain l)) 1 =
          inflatedPosition (s.chosen ε) h.data.tree (chosenLeafEquiv s.skeleton s.placement ε l).toNode := by
        unfold coupleRoot; rw [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), (s.ordinary_pair_sides ε _ hq').2, hf]; rfl
      rw [hc, hc'] at key
      rw [hmap, hν, ← key, ← hzl]
  · -- a branch other than `u₂`
    let b : GBranch s.skeleton.tree := ⟨(owner s.skeleton s.data.tree z).1, hb⟩
    have hbo : b.toNode = owner s.skeleton s.data.tree z := rfl
    have hbl : b ≠ s.placement.lower := fun e => ho (by
      rw [← hbo, e]; exact (mem_replacedNodes _ _).mpr (Or.inl rfl))
    rw [← hbo, localTree_branch] at hq
    have key : layerAt LG (addrExt (inflatedPosition s.skeleton s.data.tree b.toNode)
          (localPath s.skeleton s.data.tree z)) =
        layerAt h.output (addrExt (inflatedPosition (s.chosen ε) h.data.tree (s.branches ε b).toNode)
          (localPath s.skeleton s.data.tree z)) := h.ordinaryTreeLayers b hbl _ hq
    have hν : C.ν (owner s.skeleton s.data.tree z) = (s.branches ε b).toNode := by
      rw [← hbo, ← E.hB]; exact congrArg GBranch.toNode (hνB b)
    have hzb : z = addrExt (inflatedPosition s.skeleton s.data.tree b.toNode) (localPath s.skeleton s.data.tree z) :=
      hzq
    rw [hmap, hν]
    exact key.symm.trans (by rw [← hzb])

end Layer

/-! ## The bundled correspondence of one LF construction -/

section Bundle
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) {ε : Bool}
  (h : LFConstruction s ε) (hsame : (s.skeleton.pair s.placement.retained).1.1 = s.placement.lower.1.1)

/-- The output data is B2b's `lfReconstructionChoice`. -/
theorem data_eq_choice :
    h.data = lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple h.tree_wf
      h.couple_wf :=
  s.finalData_eq_choice ε _ _ _ _

theorem decodes_choice :
    (lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple h.tree_wf
      h.couple_wf).Decodes (chosenSkeleton_plain s.skeleton s.placement s.plain ε) h.output.garden := by
  have hd := h.decodes
  rw [data_eq_choice s h] at hd
  exact hd

/-- **The layered correspondence of one LF construction** (off the replaced region). -/
def stepIso : StepIso LG h.output where
  R := ownedBy s.skeleton s.data.tree
    (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).Rsk
  R' := ownedBy (chosenSkeleton s.skeleton s.placement ε)
    (lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple h.tree_wf
      h.couple_wf).tree
    (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).Rsk'
  I := (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).toOutIso
    s.decodes (decodes_choice s h)
    ((choicePair s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).pairTree
      s.decodes (decodes_choice s h))
  I' := (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).symm.toOutIso
    (decodes_choice s h) s.decodes
    ((choicePair s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε).symm.pairTree
      (decodes_choice s h) s.decodes)
  hinv z' hz' hR' := (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame
    ε).symm.symm_map_map (decodes_choice s h) s.decodes z' hz' hR'
  hinv' z hz hR := (choiceCoord s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame
    ε).symm_map_map s.decodes (decodes_choice s h) z hz hR
  hR := regionOK_ownedBy s.decodes _
    (by rw [choiceCoord_rsk]; exact replaced_nonroot s.placement)
    (by rw [choiceCoord_rsk]; exact replaced_pairTree s.placement hsame)
  hR' := regionOK_ownedBy (decodes_choice s h) _ (choice_rootR' _ _ _ _ _ _ _ hsame ε)
    (choice_pairR' _ _ _ _ _ _ _ hsame ε)
  hlay z hz hR := layer_map s h (data_eq_choice s h).symm _
    (choicePair s.plain s.placement s.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame ε)
    (choiceCoord_rsk _ _ _ _ _ _ _ hsame ε) (choicePair_νB _ _ _ _ _ _ _ hsame ε)
    (choicePair_νL _ _ _ _ _ _ _ hsame ε) z hz hR

theorem stepIso_R : (stepIso s h hsame).R = ownedBy s.skeleton s.data.tree (replacedNodes s.placement) := by
  show ownedBy _ _ (choiceCoord _ _ _ _ _ _ _ hsame ε).Rsk = _
  rw [choiceCoord_rsk]

end Bundle

end WaveTurbulence.Flower.CapsStable
