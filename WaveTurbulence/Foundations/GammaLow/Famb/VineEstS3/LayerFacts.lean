/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts` (sha256 1c115c3b0fa81417…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Layer facts of the vine-chain rows (TARGET regred L946-L951, standing data derived from `IsLayering`)

With `qOut 0` the layer of the core of `a` and `W.q` the layers of the cores of the interior branches, every
layer clause of `CoupleEligible` / `TreeEligible` (`q, q' ≤ p`, root layers `≤ q, q'`, `q' ≤ q` for trees, the lone
leaf layer) follows from `IsLayering` of the reconstructed garden: the layer of the attached node of a child is below
the layer of its parent's core (`core_child_position`), the layer of the core of a branch is below that of its parent's
core (`LFTwist.inducedPrelayer_isBranchPrelayering`), and the lone leaf of a native tree is the core branch
(`chainContextNode_lone`).  What remains are the order bound `size/2 ≤ N_{p+1}^4` and the coherent clause (L951).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree Reg WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem nodeSlot_parent_aΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ []) (hpa : x.parent hn = a) :
    nodeSlotΓ hM9 B x = Sum.inr 0 := by
  refine slot_ext _ _ fun t τ => ?_
  rw [← nodeSlot_specΓ hM9 B x hx hne t τ, parentClock_nonroot _ _ x hn, hpa]
  exact clLocalClock_upper R t _

theorem nodeSlot_parent_neΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ [])
    (hmem : x.parent hn ∈ clInteriorBranches R) :
    nodeSlotΓ hM9 B x = Sum.inl ((assemblyClockAtomEquivΓ hM9 B).symm ⟨x.parent hn, hmem⟩) := by
  refine slot_ext _ _ fun t τ => ?_
  rw [← nodeSlot_specΓ hM9 B x hx hne t τ, parentClock_nonroot _ _ x hn]
  have := clLocalClock_slotΓ hM9 B t τ ((assemblyClockAtomEquivΓ hM9 B).symm ⟨x.parent hn, hmem⟩)
  rw [Equiv.apply_symm_apply] at this
  rw [this]; rfl

theorem branchSlot_eqΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (v : ↥(clInteriorBranches R)) :
    branchSlotΓ hM9 B v = (assemblyClockAtomEquivΓ hM9 B).symm v := by
  classical
  have h1 : ∀ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ), τ (branchSlotΓ hM9 B v) = τ ((assemblyClockAtomEquivΓ hM9 B).symm v) := by
    intro t τ
    rw [← branchSlot_specΓ hM9 B v t τ]
    have := clLocalClock_slotΓ hM9 B t τ ((assemblyClockAtomEquivΓ hM9 B).symm v)
    have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquivΓ hM9 B) v)
    rw [h] at this
    exact this
  have := slot_ext (T := (assemblyShapeΓ hM9 B).TVar) (Sum.inl (branchSlotΓ hM9 B v))
    (Sum.inl ((assemblyClockAtomEquivΓ hM9 B).symm v)) (fun t τ => h1 t τ)
  exact Sum.inl.inj this

theorem qslot_nodeSlotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (hn : x.1.2 ≠ []) :
    qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B x) = layer (RD.coreBranch hG (x.parent hn)).toNode := by
  by_cases hpa : x.parent hn = a
  · rw [nodeSlot_parent_aΓ hM9 B x hx hne hn hpa, hpa]
    exact hqo
  · have hmem : x.parent hn ∈ clInteriorBranches R := by
      obtain ⟨hn', hp⟩ := cl_realization_parent B.isBlock R x hx hne
      exact Finset.mem_erase.mpr ⟨hpa, hp⟩
    rw [nodeSlot_parent_neΓ hM9 B x hx hne hn hmem]
    show W.q _ = _
    rw [hq]
    simp [assemblyTimeQΓ]

theorem qslot_branchSlotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (v : ↥(clInteriorBranches R)) :
    qslot (sourceSumintDatumΓ hM9 B hG W) (Sum.inl (branchSlotΓ hM9 B v)) = layer (RD.coreBranch hG v.1).toNode := by
  rw [branchSlot_eqΓ]
  show W.q _ = _
  rw [hq]
  have h := congrArg Subtype.val (Equiv.apply_symm_apply (assemblyClockAtomEquivΓ hM9 B) v)
  simp only [assemblyTimeQΓ]
  rw [h]

section Rows
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
include hLayer

/-- Layer facts at a node slot: the layer of the attached node is below the unit-interval index of the parent
clock slot, which is the layer of the parent's core branch. -/
theorem nodeSlot_factsΓ (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    layer (attachedNode RD hG x) ≤ qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B x) := by
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R x hx hne
  rw [qslot_nodeSlotΓ hM9 B RD hG layer W hq hqo x hx hne hn]
  exact layer_attached_le RD hG layer hLayer x hn

omit hLayer in
theorem qslot_leΓ (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) {p : ℕ} (hlay : ∀ x, layer x ≤ p) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B x) ≤ p := by
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R x hx hne
  rw [qslot_nodeSlotΓ hM9 B RD hG layer W hq hqo x hx hne hn]
  exact hlay _

theorem rowQ_inlΓ (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v) =
      (qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode),
       qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode)) := by
  simp [rowQΓ, assemblyClockedΓ]

theorem rowQ_inrΓ (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v) =
      (qslot (sourceSumintDatumΓ hM9 B hG W) (nodeSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v).1.toNode),
       qslot (sourceSumintDatumΓ hM9 B hG W) (Sum.inl (branchSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v)))) := by
  simp [rowQΓ, assemblyClockedΓ]

theorem coupleEligible_ofΓ (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx)
    (hsize : (rowCoupleΓ hM9 B RD hG v).size / 2 ≤ Nb)
    (hcoh : rowCoupleGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
        (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 (rowCoupleΓ hM9 B RD hG v)
        (rowCoupleLGΓ hM9 B RD hG layer hLayer v)) :
    CoupleEligibleΓ hM9 B RD hG W L γ δ F layer hLayer Nb p v := by
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOfΓ hM9 B hG v)
  have h1 := (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).1
  have h2 := (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).2
  have e := rowQ_inlΓ hM9 B RD hG layer hLayer W L γ δ F v
  refine ⟨?_, ?_, hsize, ?_, ?_, hcoh⟩
  · rw [e]; exact qslot_leΓ hM9 B RD hG layer W hq hqo hlay _ h1 hp.1
  · rw [e]; exact qslot_leΓ hM9 B RD hG layer W hq hqo hlay _ h2 hp.2
  · have r0 : (rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.tree 0) =
        layer (attachedNode RD hG ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode) :=
      congrArg layer (subforest_node_root (nativeCoupleForest RD hG (assemblyPairOfΓ hM9 B hG v).1) 0)
    rw [r0, e]
    exact nodeSlot_factsΓ hM9 B RD hG layer hLayer W hq hqo _ h1 hp.1
  · have r1 : (rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.tree 1) =
        layer (attachedNode RD hG ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode) :=
      congrArg layer (subforest_node_root (nativeCoupleForest RD hG (assemblyPairOfΓ hM9 B hG v).1) 1)
    rw [r1, e]
    exact nodeSlot_factsΓ hM9 B RD hG layer hLayer W hq hqo _ h2 hp.2

theorem treeEligible_ofΓ (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx)
    (hsize : (rowTreeΓ hM9 B RD v).size / 2 ≤ Nb)
    (hcoh : rowTreeGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
        (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 (rowTreeΓ hM9 B RD v)
        (rowTreeLGΓ hM9 B RD hG layer hLayer v)) :
    TreeEligibleΓ hM9 B RD hG W L γ δ F layer hLayer Nb p v := by
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOfΓ hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOfΓ hM9 B v).2).2
  have hne := interior_ne (assemblyBranchOfΓ hM9 B v)
  have e := rowQ_inrΓ hM9 B RD hG layer hLayer W L γ δ F v
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R _ hbr hne
  have hq1 := qslot_nodeSlotΓ hM9 B RD hG layer W hq hqo _ hbr hne hn
  have hq2 := qslot_branchSlotΓ hM9 B RD hG layer W hq (assemblyBranchOfΓ hM9 B v)
  have hcl := layer_core_le RD hG layer hLayer (assemblyBranchOfΓ hM9 B v).1 hn
  refine ⟨?_, ?_, hsize, ?_, ?_, hcoh⟩
  · rw [e]; dsimp only
    rw [hq1, hq2]; exact hcl
  · rw [e]; dsimp only
    rw [hq1]; exact hlay _
  · have r0 : (rowTreeLGΓ hM9 B RD hG layer hLayer v).layer
        (GNode.root (rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.tree 0) =
        layer (attachedNode RD hG (assemblyBranchOfΓ hM9 B v).1.toNode) :=
      congrArg layer (chainContextNode_root RD hG (assemblyBranchOfΓ hM9 B v).1)
    rw [r0, e]
    exact nodeSlot_factsΓ hM9 B RD hG layer hLayer W hq hqo _ hbr hne
  · intro x hx
    have hxe : x = (chainLoneLeaf (RD.tree (assemblyBranchOfΓ hM9 B v).1)
        (nodeSign G.sig (assemblyBranchOfΓ hM9 B v).1.1)).toNode := by
      apply Subtype.ext
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact hx
    have : (rowTreeLGΓ hM9 B RD hG layer hLayer v).layer x = layer (RD.coreBranch hG (assemblyBranchOfΓ hM9 B v).1).toNode := by
      show layer (chainContextNode RD hG (assemblyBranchOfΓ hM9 B v).1 x) = _
      rw [hxe, chainContextNode_lone]
    rw [this, e]
    dsimp only
    rw [hq2]

/-- Standing order bounds `n_ρ ≤ N_{p+1}^4` of the regular objects (TARGET L951). -/
def RowSizesΓ (Nb : ℕ) : Prop :=
  ∀ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2 ≤ Nb ∧ (rowTreeΓ hM9 B RD v).size / 2 ≤ Nb

/-- **The coherent eligibility premise (TARGET L946-L951).**  A regular couple or tree of incoherency index `0`
occurring in the chain is coherent, i.e. embeds in the canonical garden (`IsCoherentCoupleAt`, `IsCoherentTreeAt`),
for both orientations of the two leaf layers (the `q < q'` case is the conjugate couple, `ConjCoh.couple_row_le_both`). -/
def RowCoherentΓ (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (p : ℕ) : Prop :=
  ∀ v : (assemblyShapeΓ hM9 B).VIdx,
    (rowCoupleGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
        (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 (rowCoupleΓ hM9 B RD hG v)
        (rowCoupleLGΓ hM9 B RD hG layer hLayer v)) ∧
    (rowTreeGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
        (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2 (rowTreeΓ hM9 B RD v)
        (rowTreeLGΓ hM9 B RD hG layer hLayer v))

theorem eligible_ofΓ (hq : W.q = assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (Nb p : ℕ)
    (hlay : ∀ x, layer x ≤ p) (hs : RowSizesΓ hM9 B RD hG Nb)
    (hc : RowCoherentΓ hM9 B RD hG layer hLayer W L γ δ F p) (v : (assemblyShapeΓ hM9 B).VIdx) :
    CoupleEligibleΓ hM9 B RD hG W L γ δ F layer hLayer Nb p v ∧
      TreeEligibleΓ hM9 B RD hG W L γ δ F layer hLayer Nb p v :=
  ⟨coupleEligible_ofΓ hM9 B RD hG layer hLayer W hq hqo L γ δ F Nb p hlay v (hs v).1 (hc v).1,
   treeEligible_ofΓ hM9 B RD hG layer hLayer W hq hqo L γ δ F Nb p hlay v (hs v).2 (hc v).2⟩

omit hLayer in
theorem assemblyTimeQ_firstΓ (hI : 0 < (assemblyShapeΓ hM9 B).I) :
    assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) (.inl ⟨⟨0, hI⟩, 0⟩) =
      layer (RD.coreBranch hG b).toNode := by
  simp only [assemblyTimeQΓ]
  rw [assemblyClockAtom_firstΓ hM9 B hI]

/-- The unit-interval index of a lower child is at most the lower window end of the lower joint. -/
theorem qOutOf_one_leΓ (hI : 0 < (assemblyShapeΓ hM9 B).I) :
    (qOutOf RD hG layer a b R 1 : ℝ) ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
      (.inl ⟨⟨0, hI⟩, 0⟩) := by
  rw [assemblyTimeQ_firstΓ hM9 B RD hG layer hI]
  show (layer (outNode RD hG (b.child R.positive)) : ℝ) ≤ _
  exact_mod_cast layer_outNode_le RD hG layer hLayer b _

theorem qOutOf_two_leΓ (hI : 0 < (assemblyShapeΓ hM9 B).I) :
    (qOutOf RD hG layer a b R 2 : ℝ) ≤ assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
      (.inl ⟨⟨0, hI⟩, 0⟩) := by
  rw [assemblyTimeQ_firstΓ hM9 B RD hG layer hI]
  show (layer (outNode RD hG (b.child R.negative)) : ℝ) ≤ _
  exact_mod_cast layer_outNode_le RD hG layer hLayer b _

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS3
