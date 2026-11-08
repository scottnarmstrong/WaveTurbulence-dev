/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.IdStep

/-! # B2b MK-MARK: near regions across one LF step

`NearRel S o b`: the skeleton node `o` is `b`, a child of `b`, or the partner of a leaf child of `b` (so an address
lies in `nearRegion S X b` iff its owner is near `b`, `mem_nearRegion_iff`).

* `markedBranch_transport`: for coordinate data `C` whose node map respects `NearRel` off the replaced nodes,
  "the near region of `b` contains a vertex of `Π₀`" is transported from `b` to `νB b`, when both `Π₀`'s avoid the
  replaced regions and correspond off them.
* `twist_nearRel`: the naive node bijection of a unit twist respects `NearRel` off `{u₂, u₂₃, u₀}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- `o` is near the branch `b`. -/
def NearRel (S : Garden w) (o : GNode S.tree) (b : GBranch S.tree) : Prop :=
  o = b.toNode ∨ (∃ i, o = b.child i) ∨ ∃ ℓ : GLeaf S.tree, b.IsParentOf ℓ ∧ o = (S.pair ℓ).toNode

theorem mem_nearRegion_iff' (S : Garden w) (X : GBranch S.tree → RegChain) {y : Address w} {b : GBranch S.tree} :
    y ∈ nearRegion S X b ↔ NearRel S (owner S X y) b := mem_nearRegion_iff S X

/-- The near region of `b` contains a protected vertex. -/
def MarkedBranch (S : Garden w) (X : GBranch S.tree → RegChain) {T : Fin w → TTree} (Pi : Finset (GNode T))
    (b : GBranch S.tree) : Prop :=
  ∃ a ∈ Pi, a.1 ∈ nearRegion S X b

namespace CoordData
variable {S S' : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {D' : ReconstructionData S'}
  {hS' : S'.IsPlain} (C : CoordData D hS D' hS')
  {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden) (hd' : D'.Decodes hS' LG'.garden)

include hd hd' in
/-- **Marked branches are transported.** -/
theorem markedBranch_transport {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ)
    (νB : GBranch S.tree → GBranch S'.tree)
    (hnear : ∀ o, o ∉ C.Rsk → ∀ b, NearRel S o b ↔ NearRel S' (C.ν o) (νB b))
    (hp : NoProtIn LG J pat (ownedBy S D.tree C.Rsk)) (hp' : NoProtIn LG' J pat (ownedBy S' D'.tree C.Rsk'))
    (hiff : ∀ z, NodeAt LG z → z ∉ ownedBy S D.tree C.Rsk → (ProtAt LG' J pat (C.map z) ↔ ProtAt LG J pat z))
    (b : GBranch S.tree) :
    MarkedBranch S D.tree (protI0 LG J pat t s) b ↔ MarkedBranch S' D'.tree (protI0 LG' J pat t s) (νB b) := by
  constructor
  · rintro ⟨a, ha, hab⟩
    have hpa := (mem_protI0_iff_protAt pat t s a).mp ha
    have hR : a.1 ∉ ownedBy S D.tree C.Rsk := fun h => hp _ h hpa
    have hn := C.map_node hd hd' a.1 a.2 hR
    have hpa' := (hiff a.1 a.2 hR).mpr hpa
    refine ⟨⟨C.map a.1, hn.1⟩, (mem_protI0_iff_protAt pat t s _).mpr hpa', ?_⟩
    rw [mem_nearRegion_iff'] at hab ⊢
    rw [hn.2]
    exact (hnear _ hR b).mp hab
  · rintro ⟨a', ha', hab'⟩
    have hpa' := (mem_protI0_iff_protAt pat t s a').mp ha'
    have hR' : a'.1 ∉ ownedBy S' D'.tree C.Rsk' := fun h => hp' _ h hpa'
    have hn := C.symm.map_node hd' hd a'.1 a'.2 hR'
    have hR : C.symm.map a'.1 ∉ ownedBy S D.tree C.Rsk := C.symm.map_owner_not hd' hd a'.1 a'.2 hR'
    have hinv : C.map (C.symm.map a'.1) = a'.1 := C.symm.symm_map_map hd' hd a'.1 a'.2 hR'
    have hpa : ProtAt LG J pat (C.symm.map a'.1) := (hiff _ hn.1 hR).mp (by rw [hinv]; exact hpa')
    refine ⟨⟨C.symm.map a'.1, hn.1⟩, (mem_protI0_iff_protAt pat t s _).mpr hpa, ?_⟩
    rw [mem_nearRegion_iff'] at hab' ⊢
    have ho : owner S D.tree (C.symm.map a'.1) ∉ C.Rsk := hR
    apply (hnear _ ho b).mpr
    have e : C.ν (owner S D.tree (C.symm.map a'.1)) = owner S' D'.tree a'.1 := by
      rw [hn.2]
      exact Equiv.apply_symm_apply _ _
    rw [e]
    exact hab'

end CoordData

theorem isParentOf_iff {tree : Fin w → TTree} (b : GBranch tree) (ℓ : GLeaf tree) :
    b.IsParentOf ℓ ↔ ∃ i, ℓ.toNode = b.child i := by
  constructor
  · rintro ⟨h1, i, h2⟩
    exact ⟨i, Subtype.ext (Prod.ext h1 h2)⟩
  · rintro ⟨i, h⟩
    have hv : ℓ.1 = (b.1.1, b.1.2 ++ [i]) := congrArg Subtype.val h
    exact ⟨by rw [hv], i, by rw [hv]⟩

section TwistNear
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

omit hS in
theorem exchangeChildSlot_invol (p : Address w) (j : Fin 3) :
    exchangeChildSlot P.lower.1 P.keep p (exchangeChildSlot P.lower.1 P.keep p j) = j := by
  unfold exchangeChildSlot
  split_ifs
  · exact freeSwap_involutive _ _
  · rfl

omit hS in
theorem replaced_pair_closed' (l : GLeaf S.tree) (hl : (S.pair l).toNode ∉ replacedNodes P) :
    l.toNode ∉ replacedNodes P := by
  have := replaced_pair_closed P (S.pair l) hl
  rwa [S.pair_pair] at this

include hS D X Q hX hQ hsame in
/-- Backward child step of the naive node bijection off the replaced nodes. -/
theorem twist_child_bwd (o : GNode S.tree) (ho : o ∉ replacedNodes P) (b : GBranch S.tree) (j : Fin 3)
    (h : naiveNodeEquiv S P o = (coreBranchEquiv S P b).child j) : ∃ i, o = b.child i := by
  set i := exchangeChildSlot P.lower.1 P.keep b.1 j
  by_cases hc : b.child i = P.lower.toNode ∨ b.child i = (S.pair P.retained).toNode
  · exfalso
    have hbl : b ≠ P.lower := by
      rintro rfl
      rcases hc with hc | hc
      · have := congrArg (fun x : GNode S.tree => x.1.2.length) hc
        simp [GBranch.child, GBranch.toNode] at this
      · apply P.paired_outside
        rw [← hc]
        exact GBranch.isDesc_child _ _
    have hb : b.toNode ∉ replacedNodes P := by
      rw [mem_replacedNodes, not_or, not_or]
      exact ⟨fun e => hbl (Subtype.ext (by exact congrArg (fun x : GNode S.tree => x.1) e)), leaf_ne_branch _ _ ∘ Eq.symm,
        leaf_ne_branch _ _ ∘ Eq.symm⟩
    have hij : i = j := by
      show exchangeChildSlot P.lower.1 P.keep b.1 j = j
      unfold exchangeChildSlot
      rw [if_neg (fun e => hbl (Subtype.ext e))]
    have hin : b.child i ∈ replacedNodes P := by
      rw [mem_replacedNodes]
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inr hc)
    have := ((twistCoord hS P D X Q hX hQ hsame).child b (coreBranchEquiv S P b) hb
      (naiveNodeEquiv_branch S P b).symm i).1.mp hin
    change (naiveNodeEquiv S P).symm ((coreBranchEquiv S P b).child i) ∈ replacedNodes P at this
    rw [hij, ← h, Equiv.symm_apply_apply] at this
    exact ho this
  · rw [not_or] at hc
    refine ⟨i, ?_⟩
    apply (naiveNodeEquiv S P).injective
    rw [h, naiveNodeEquiv_child S P (p := b) (n := b.child i) (i := i) rfl hc.1 hc.2, exchangeChildSlot_invol]

include hS D X Q hX hQ hsame in
/-- **The naive node bijection respects `NearRel` off the replaced nodes.** -/
theorem twist_nearRel (o : GNode S.tree) (ho : o ∉ replacedNodes P) (b : GBranch S.tree) :
    NearRel S o b ↔ NearRel (unitTwistGarden S P) (naiveNodeEquiv S P o) (coreBranchEquiv S P b) := by
  have ho' := ho
  rw [mem_replacedNodes, not_or, not_or] at ho'
  obtain ⟨h1, -, h3⟩ := ho'
  constructor
  · rintro (h | ⟨i, h⟩ | ⟨ℓ, hℓ, h⟩)
    · left
      rw [h, naiveNodeEquiv_branch]
      rfl
    · right; left
      exact ⟨_, naiveNodeEquiv_child S P h h1 h3⟩
    · right; right
      have hℓR : ℓ.toNode ∉ replacedNodes P := replaced_pair_closed' P ℓ (by rw [← h]; exact ho)
      rw [mem_replacedNodes, not_or, not_or] at hℓR
      obtain ⟨i, hi⟩ := (isParentOf_iff b ℓ).mp hℓ
      have hc := naiveNodeEquiv_child S P hi hℓR.1 hℓR.2.2
      rw [naiveNodeEquiv_leaf] at hc
      refine ⟨coreLeafEquiv S P ℓ, (isParentOf_iff _ _).mpr ⟨_, hc⟩, ?_⟩
      rw [h, naiveNodeEquiv_leaf, unitTwistGarden_pair]
      rfl
  · rintro (h | ⟨j, h⟩ | ⟨ℓ', hℓ', h⟩)
    · left
      apply (naiveNodeEquiv S P).injective
      rw [h, naiveNodeEquiv_branch]
      rfl
    · right; left
      exact twist_child_bwd hS P D X Q hX hQ hsame o ho b j h
    · right; right
      set ℓ := (coreLeafEquiv S P).symm ℓ'
      have hℓ'e : ℓ' = coreLeafEquiv S P ℓ := (Equiv.apply_symm_apply _ _).symm
      have ho2 : o = (S.pair ℓ).toNode := by
        apply (naiveNodeEquiv S P).injective
        rw [h, naiveNodeEquiv_leaf, hℓ'e, unitTwistGarden_pair]
        rfl
      have hℓR : ℓ.toNode ∉ replacedNodes P := replaced_pair_closed' P ℓ (by rw [← ho2]; exact ho)
      obtain ⟨j, hj⟩ := (isParentOf_iff _ _).mp hℓ'
      have hν : naiveNodeEquiv S P ℓ.toNode = (coreBranchEquiv S P b).child j := by
        rw [naiveNodeEquiv_leaf, ← hℓ'e]
        exact hj
      obtain ⟨i, hi⟩ := twist_child_bwd hS P D X Q hX hQ hsame ℓ.toNode hℓR b j hν
      exact ⟨ℓ, (isParentOf_iff b ℓ).mpr ⟨i, hi⟩, ho2⟩

end TwistNear

end WaveTurbulence.Flower.MkMark
