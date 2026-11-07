/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering

/-! # Layer facts of the vine-chain rows (TARGET regred L946-L951, standing data derived from `IsLayering`)

With `qOut 0` the layer of the core of `a` and `W.q` the layers of the cores of the interior branches, every
layer clause of `CoupleEligible` / `TreeEligible` (`q, q' ≤ p`, root layers `≤ q, q'`, `q' ≤ q` for trees, the lone
leaf layer) follows from `IsLayering` of the reconstructed garden: the layer of the attached node of a child is below
the layer of its parent's core (`core_child_position`), the layer of the core of a branch is below that of its parent's
core (`LFTwist.inducedPrelayer_isBranchPrelayering`), and the lone leaf of a native tree is the core branch
(`chainContextNode_lone`).  What remains are the order bound `size/2 ≤ N_{p+1}^4` and the coherent clause (L951).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree Reg
  Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem slot_ext {T : Type} (s s' : T ⊕ Fin 3)
    (h : ∀ (t : Fin 3 → ℝ) (τ : T → ℝ), Sum.elim τ t s = Sum.elim τ t s') : s = s' := by
  classical
  rcases s with s | c <;> rcases s' with s' | c'
  · by_contra hne
    have hne' : s' ≠ s := fun e => hne (by rw [e])
    have := h 0 (Pi.single s 1)
    simp [Pi.single_apply, hne'] at this
  · have := h 0 (fun _ => 1)
    simp at this
  · have := h (fun _ => 1) 0
    simp at this
  · by_contra hne
    have hne' : c' ≠ c := fun e => hne (by rw [e])
    have := h (Pi.single c 1) 0
    simp [Pi.single_apply, hne'] at this



theorem nodeSlot_parent_a (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ []) (hpa : x.parent hn = a) :
    nodeSlot hM9 B x = Sum.inr 0 := by
  refine slot_ext _ _ fun t τ => ?_
  rw [← nodeSlot_spec hM9 B x hx hne t τ, parentClock_nonroot _ _ x hn, hpa]
  exact clLocalClock_upper R t _

theorem nodeSlot_parent_ne (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ [])
    (hmem : x.parent hn ∈ clInteriorBranches R) :
    nodeSlot hM9 B x = Sum.inl ((assemblyClockAtomEquiv hM9 B).symm ⟨x.parent hn, hmem⟩) := by
  refine slot_ext _ _ fun t τ => ?_
  rw [← nodeSlot_spec hM9 B x hx hne t τ, parentClock_nonroot _ _ x hn]
  have := clLocalClock_slot hM9 B t τ ((assemblyClockAtomEquiv hM9 B).symm ⟨x.parent hn, hmem⟩)
  rw [Equiv.apply_symm_apply] at this
  rw [this]; rfl

theorem branchSlot_eq (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (v : ↥(clInteriorBranches R)) :
    branchSlot hM9 B v = (assemblyClockAtomEquiv hM9 B).symm v := by
  classical
  have h1 : ∀ (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ), τ (branchSlot hM9 B v) = τ ((assemblyClockAtomEquiv hM9 B).symm v) := by
    intro t τ
    rw [← branchSlot_spec hM9 B v t τ]
    have := clLocalClock_slot hM9 B t τ ((assemblyClockAtomEquiv hM9 B).symm v)
    have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquiv hM9 B) v)
    rw [h] at this
    exact this
  have := slot_ext (T := (assemblyShape hM9 B).TVar) (Sum.inl (branchSlot hM9 B v))
    (Sum.inl ((assemblyClockAtomEquiv hM9 B).symm v)) (fun t τ => h1 t τ)
  exact Sum.inl.inj this



theorem qslot_nodeSlot (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ []) :
    qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B x) = layer (RD.coreBranch hG (x.parent hn)).toNode := by
  by_cases hpa : x.parent hn = a
  · rw [nodeSlot_parent_a hM9 B x hx hne hn hpa, hpa]
    exact hqo
  · have hmem : x.parent hn ∈ clInteriorBranches R := by
      obtain ⟨hn', hp⟩ := cl_realization_parent B.isBlock R x hx hne
      exact Finset.mem_erase.mpr ⟨hpa, hp⟩
    rw [nodeSlot_parent_ne hM9 B x hx hne hn hmem]
    show W.q _ = _
    rw [hq]
    simp [assemblyTimeQ]

theorem qslot_branchSlot (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (v : ↥(clInteriorBranches R)) :
    qslot (sourceSumintDatum hM9 B hG W) (Sum.inl (branchSlot hM9 B v)) = layer (RD.coreBranch hG v.1).toNode := by
  rw [branchSlot_eq]
  show W.q _ = _
  rw [hq]
  have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquiv hM9 B) v)
  simp only [assemblyTimeQ]
  rw [h]



theorem attached_child_eq (RD : ReconstructionData G) (hG : G.IsPlain) (c : GBranch G.tree) (i : Fin 3) :
    attachedNode RD hG (c.child i) = (RD.coreBranch hG c).child i :=
  Subtype.ext (RD.core_child_position c i)

theorem layer_attached_le (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (x : GNode G.tree) (hn : x.1.2 ≠ []) :
    layer (attachedNode RD hG x) ≤ layer (RD.coreBranch hG (x.parent hn)).toNode := by
  have h := Mole.parent_child_eq_node x hn
  have h2 : attachedNode RD hG x = (RD.coreBranch hG (x.parent hn)).child (List.getLast x.1.2 hn) := by
    rw [← attached_child_eq, h]
  rw [h2]
  exact hLayer.1 _ _

theorem layer_core_le (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c : GBranch G.tree) (hn : c.toNode.1.2 ≠ []) :
    layer (RD.coreBranch hG c).toNode ≤ layer (RD.coreBranch hG (c.toNode.parent hn)).toNode := by
  have h1 := LFTwist.inducedPrelayer_isBranchPrelayering (layeredReconstruction RD hG layer hLayer) RD hG
    (RD.garden_decodes hG) (c.toNode.parent hn) c (List.getLast c.toNode.1.2 hn) (Mole.parent_child_eq_node c.toNode hn).symm
  exact h1

/-- The node of the reconstructed garden whose layer is the unit-interval index of a skeleton node `c'` which is a child
of the lower joint (F-QOUT): the core branch of `c'` when `c'` is a branch (its clock is the clock of the core,
TARGET (redkg) L1726), and the attached node, the leaf itself, when `c'` is a leaf. -/
noncomputable def outNode (RD : ReconstructionData G) (hG : G.IsPlain) (c' : GNode G.tree) : GNode (RD.forest hG) :=
  if hb : c'.1.2 ∈ (G.tree c'.1.1).branching then (RD.coreBranch hG ⟨c'.1, hb⟩).toNode else attachedNode RD hG c'

/-- **F-QOUT.**  The layer of the output node of a child of the joint `b` is at most the layer of the core of `b`.
For a branch child `c` this is monotonicity of the induced branch layering on the cores; for a leaf child it is
`attached_child_eq` and the layering. -/
theorem layer_outNode_le (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (b : GBranch G.tree) (i : Fin 3) :
    layer (outNode RD hG (b.child i)) ≤ layer (RD.coreBranch hG b).toNode := by
  unfold outNode
  split_ifs with hb
  · exact LFTwist.inducedPrelayer_isBranchPrelayering (layeredReconstruction RD hG layer hLayer) RD hG
      (RD.garden_decodes hG) b ⟨(b.child i).1, hb⟩ i rfl
  · rw [attached_child_eq]
    exact hLayer.1 _ _



section Rows
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (assemblyShape hM9 B) d)
include hLayer

/-- Layer facts at a node slot: the layer of the attached node is below the unit-interval index of the parent
clock slot, which is the layer of the parent's core branch. -/
theorem nodeSlot_facts (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    layer (attachedNode RD hG x) ≤ qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B x) := by
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R x hx hne
  rw [qslot_nodeSlot hM9 B RD hG layer W hq hqo x hx hne hn]
  exact layer_attached_le RD hG layer hLayer x hn



omit hLayer in
theorem qslot_le (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) {p : ℕ} (hlay : ∀ x, layer x ≤ p) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B x) ≤ p := by
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R x hx hne
  rw [qslot_nodeSlot hM9 B RD hG layer W hq hqo x hx hne hn]
  exact hlay _

theorem rowQ_inl (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (v : (assemblyShape hM9 B).VIdx) :
    rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v) =
      (qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode),
       qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode)) := by
  simp [rowQ, assemblyClocked]

theorem rowQ_inr (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (v : (assemblyShape hM9 B).VIdx) :
    rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v) =
      (qslot (sourceSumintDatum hM9 B hG W) (nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode),
       qslot (sourceSumintDatum hM9 B hG W) (Sum.inl (branchSlot hM9 B (assemblyBranchOf hM9 B v)))) := by
  simp [rowQ, assemblyClocked]



theorem coupleEligible_of (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hsize : (rowCouple hM9 B RD hG v).size / 2 ≤ Nb)
    (hcoh : rowCoupleG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 (rowCouple hM9 B RD hG v)
        (rowCoupleLG hM9 B RD hG layer hLayer v)) :
    CoupleEligible hM9 B RD hG W L γ δ F layer hLayer Nb p v := by
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1
  have h2 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2
  have e := rowQ_inl hM9 B RD hG layer hLayer W L γ δ F v
  refine ⟨?_, ?_, hsize, ?_, ?_, hcoh⟩
  · rw [e]; exact qslot_le hM9 B RD hG layer W hq hqo hlay _ h1 hp.1
  · rw [e]; exact qslot_le hM9 B RD hG layer W hq hqo hlay _ h2 hp.2
  · have r0 : (rowCoupleLG hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowCoupleLG hM9 B RD hG layer hLayer v).garden.tree 0) =
        layer (attachedNode RD hG ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode) :=
      congrArg layer (subforest_node_root (nativeCoupleForest RD hG (assemblyPairOf hM9 B hG v).1) 0)
    rw [r0, e]
    exact nodeSlot_facts hM9 B RD hG layer hLayer W hq hqo _ h1 hp.1
  · have r1 : (rowCoupleLG hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowCoupleLG hM9 B RD hG layer hLayer v).garden.tree 1) =
        layer (attachedNode RD hG ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode) :=
      congrArg layer (subforest_node_root (nativeCoupleForest RD hG (assemblyPairOf hM9 B hG v).1) 1)
    rw [r1, e]
    exact nodeSlot_facts hM9 B RD hG layer hLayer W hq hqo _ h2 hp.2



theorem treeEligible_of (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hsize : (rowTree hM9 B RD v).size / 2 ≤ Nb)
    (hcoh : rowTreeG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 (rowTree hM9 B RD v)
        (rowTreeLG hM9 B RD hG layer hLayer v)) :
    TreeEligible hM9 B RD hG W L γ δ F layer hLayer Nb p v := by
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have hne := interior_ne (assemblyBranchOf hM9 B v)
  have e := rowQ_inr hM9 B RD hG layer hLayer W L γ δ F v
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R _ hbr hne
  have hq1 := qslot_nodeSlot hM9 B RD hG layer W hq hqo _ hbr hne hn
  have hq2 := qslot_branchSlot hM9 B RD hG layer W hq (assemblyBranchOf hM9 B v)
  have hcl := layer_core_le RD hG layer hLayer (assemblyBranchOf hM9 B v).1 hn
  refine ⟨?_, ?_, hsize, ?_, ?_, hcoh⟩
  · rw [e]; dsimp only
    rw [hq1, hq2]; exact hcl
  · rw [e]; dsimp only
    rw [hq1]; exact hlay _
  · have r0 : (rowTreeLG hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowTreeLG hM9 B RD hG layer hLayer v).garden.tree 0) =
        layer (attachedNode RD hG (assemblyBranchOf hM9 B v).1.toNode) :=
      congrArg layer (chainContextNode_root RD hG (assemblyBranchOf hM9 B v).1)
    rw [r0, e]
    exact nodeSlot_facts hM9 B RD hG layer hLayer W hq hqo _ hbr hne
  · intro x hx
    have hxe : x = (chainLoneLeaf (RD.tree (assemblyBranchOf hM9 B v).1)
        (nodeSign G.sig (assemblyBranchOf hM9 B v).1.1)).toNode := by
      apply Subtype.ext
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact hx
    have : (rowTreeLG hM9 B RD hG layer hLayer v).layer x = layer (RD.coreBranch hG (assemblyBranchOf hM9 B v).1).toNode := by
      show layer (chainContextNode RD hG (assemblyBranchOf hM9 B v).1 x) = _
      rw [hxe, chainContextNode_lone]
    rw [this, e]
    dsimp only
    rw [hq2]



/-- The unit-interval indices of the three output times `(t, t', t'')`: the layers of the core of `a` and the
layers of the cores (branch children) or of the leaves (leaf children) of the two excluded lower children of `b`. -/
noncomputable def qOutOf (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (a b : GBranch G.tree) (R : CLRegionData G U a b) : Fin 3 → ℕ :=
  ![layer (RD.coreBranch hG a).toNode, layer (outNode RD hG (b.child R.positive)),
    layer (outNode RD hG (b.child R.negative))]

/-- Standing order bounds `n_ρ ≤ N_{p+1}^4` of the regular objects (TARGET L951). -/
def RowSizes (Nb : ℕ) : Prop :=
  ∀ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2 ≤ Nb ∧ (rowTree hM9 B RD v).size / 2 ≤ Nb

/-- **The coherent eligibility premise (TARGET L946-L951).**  A regular couple or tree of incoherency index `0`
occurring in the chain is coherent, i.e. embeds in the canonical garden (`IsCoherentCoupleAt`, `IsCoherentTreeAt`),
for both orientations of the two leaf layers (the `q < q'` case is the conjugate couple, `ConjCoh.couple_row_le_both`). -/
def RowCoherent (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (p : ℕ) : Prop :=
  ∀ v : (assemblyShape hM9 B).VIdx,
    (rowCoupleG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 (rowCouple hM9 B RD hG v)
        (rowCoupleLG hM9 B RD hG layer hLayer v)) ∧
    (rowTreeG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
        (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 (rowTree hM9 B RD v)
        (rowTreeLG hM9 B RD hG layer hLayer v))

theorem eligible_of (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (hs : RowSizes hM9 B RD hG Nb)
    (hc : RowCoherent hM9 B RD hG layer hLayer W L γ δ F p) (v : (assemblyShape hM9 B).VIdx) :
    CoupleEligible hM9 B RD hG W L γ δ F layer hLayer Nb p v ∧
      TreeEligible hM9 B RD hG W L γ δ F layer hLayer Nb p v :=
  ⟨coupleEligible_of hM9 B RD hG layer hLayer W hq hqo L γ δ F Nb p hlay v (hs v).1 (hc v).1,
   treeEligible_of hM9 B RD hG layer hLayer W hq hqo L γ δ F Nb p hlay v (hs v).2 (hc v).2⟩


omit hLayer in
theorem assemblyTimeQ_first (hI : 0 < (assemblyShape hM9 B).I) :
    assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) (.inl ⟨⟨0, hI⟩, 0⟩) =
      layer (RD.coreBranch hG b).toNode := by
  simp only [assemblyTimeQ]
  rw [assemblyClockAtom_first hM9 B hI]

/-- The unit-interval index of a lower child is at most the lower window end of the lower joint. -/
theorem qOutOf_one_le (hI : 0 < (assemblyShape hM9 B).I) :
    (qOutOf RD hG layer a b R 1 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
      (.inl ⟨⟨0, hI⟩, 0⟩) := by
  rw [assemblyTimeQ_first hM9 B RD hG layer hI]
  show (layer (outNode RD hG (b.child R.positive)) : ℝ) ≤ _
  exact_mod_cast layer_outNode_le RD hG layer hLayer b _

theorem qOutOf_two_le (hI : 0 < (assemblyShape hM9 B).I) :
    (qOutOf RD hG layer a b R 2 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
      (.inl ⟨⟨0, hI⟩, 0⟩) := by
  rw [assemblyTimeQ_first hM9 B RD hG layer hI]
  show (layer (outNode RD hG (b.child R.negative)) : ℝ) ≤ _
  exact_mod_cast layer_outNode_le RD hG layer hLayer b _

end Rows

end WaveTurbulence.VineEstS3
