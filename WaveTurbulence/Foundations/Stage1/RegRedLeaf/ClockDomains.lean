/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeFactorIdentities
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.TimeDomainReconstruction
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PairedTreeLowerClock

/-! # Source time domains with one exterior upper clock per root (REGRED-LEAF)

REGRED states the time-domain decomposition for a single exterior time `top`.  The stage-1 gate has an
upper time `tt j` per root `j`, so we redo `TimeDomain` / `DescendantClocks` / `NativeParentClocks` /
`NativeClockTransport` / `NativeTimeDomainForward` / `TimeDomainReconstruction` with the root-dependent
clock `parentClockWith top` (`top : Fin w → ℝ`).  The paired trees keep a single exterior clock. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton WaveTurbulence.RegRed

/-- Branch-only time domain with an exterior clock per root. -/
def coreTimeDomainW {w : ℕ} {tree : Fin w → TTree}
    (layer : GBranch tree → ℕ) (top : Fin w → ℝ) : Set (GBranch tree → ℝ) :=
  {τ | ∀ b, (layer b : ℝ) < τ b ∧ τ b < layer b + 1 ∧ 0 < τ b ∧
    τ b < parentClockWith top τ b.toNode}

/-- For an ordinary layered garden, the literal domain is the original-parent clock domain. -/
theorem kDomain_eq_coreTimeDomainW {w : ℕ} (LG : LayeredGarden w)
    (hG : LG.garden.IsPlain) (top : Fin w → ℝ) (s : ℝ) :
    kDomain LG (fun b => top b.1.1) s = coreTimeDomainW (fun b => LG.layer b.toNode) top := by
  rw [kDomain_eq_edgeTimeDomain]
  ext τ
  constructor
  · intro h b
    exact ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.1⟩
  · intro h b
    exact ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2,
      fun hl => (not_loneParent_of_plain LG.garden hG b hl).elim⟩

theorem branchTime_lt_parentClockWith_of_desc {w : ℕ} {tree : Fin w → TTree}
    (top : Fin w → ℝ) (τ : GBranch tree → ℝ) (hτ : ∀ b, τ b < parentClockWith top τ b.toNode)
    (a : GNode tree) (b : GBranch tree) (hd : a.IsDesc b.toNode) :
    τ b < parentClockWith top τ a := by
  by_cases he : a.1.2 = b.1.2
  · have hab : a = b.toNode := Subtype.ext (Prod.ext hd.1 he)
    exact hab ▸ hτ b
  · have hb : b.1.2 ≠ [] := by
      intro hz
      have hp : a.1.2 <+: [] := hz ▸ hd.2
      apply he
      exact (List.prefix_nil.mp hp).trans hz.symm
    have hparent : a.IsDesc (b.toNode.parent hb).toNode :=
      ⟨hd.1, prefix_dropLast_of_ne hd.2 he⟩
    have ht := hτ b
    change τ b < parentClockWith top τ b.toNode at ht
    rw [parentClockWith_nonroot top τ b.toNode hb] at ht
    exact ht.trans (branchTime_lt_parentClockWith_of_desc top τ hτ a (b.toNode.parent hb) hparent)
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hp : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

theorem parentClockWith_attachedNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) (a : GNode S.tree) :
    parentClockWith top τ (attachedNode D hS a) =
      parentClockWith top (fun b => τ (D.coreBranch hS b)) a := by
  obtain ⟨s, rfl⟩ := (nodeSlotEquiv S.tree).symm.surjective a
  rcases s with j | ⟨b, i⟩
  · exact (congrArg (parentClockWith top τ) (attachedNode_root D hS j)).trans
      (parentClockWith_root _ _ _ j)
  · exact (congrArg (parentClockWith top τ) (attachedNode_child D hS b i)).trans
      ((parentClockWith_child top τ _ i).trans
        (parentClockWith_child top (fun b => τ (D.coreBranch hS b)) b i).symm)

theorem subforest_parentClockWith {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (top : Fin w → ℝ) (τ : GBranch tree → ℝ) (a : GNode E.shape) :
    parentClockWith top τ (E.nodeEmbedding a) =
      parentClockWith (fun j => parentClockWith top τ (E.root j))
        (fun b => τ (subforestBranchEmbedding E b)) a := by
  obtain ⟨s, rfl⟩ := (nodeSlotEquiv E.shape).symm.surjective a
  rcases s with j | ⟨b, i⟩
  · exact congrArg (parentClockWith top τ) (subforest_node_root E j)
  · exact (congrArg (parentClockWith top τ) (subforest_node_child E b i)).trans
      ((parentClockWith_child top τ _ i).trans
        (parentClockWith_child (fun j => parentClockWith top τ (E.root j))
          (fun b => τ (subforestBranchEmbedding E b)) b i).symm)

theorem chain_parentClockWith {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    parentClockWith top τ (chainContextNode D hS b a) =
      parentClock (parentClockWith top (fun b => τ (D.coreBranch hS b)) b.toNode)
        (nativeChainClock D hS τ b) a := by
  obtain ⟨s, rfl⟩ := (nodeSlotEquiv (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree).symm.surjective a
  rcases s with j | ⟨q, i⟩
  · fin_cases j
    exact (congrArg (parentClockWith top τ) (chainContextNode_root D hS b)).trans
      (parentClockWith_attachedNode D hS top τ b.toNode)
  · exact (congrArg (parentClockWith top τ) (chainContextNode_child D hS b q i)).trans
      ((parentClockWith_child top τ _ i).trans (parentClock_child _ (nativeChainClock D hS τ b) q i).symm)

theorem core_parentClockWith_as_chain_lone {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree) :
    parentClockWith top τ (D.coreBranch hS b).toNode =
      parentClock (parentClockWith top (fun b => τ (D.coreBranch hS b)) b.toNode)
        (nativeChainClock D hS τ b) (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode :=
  (congrArg (parentClockWith top τ) (chainContextNode_lone D hS b)).symm.trans
    (chain_parentClockWith D hS top τ b _)

/-- The exterior clocks of the native couple: the skeleton clocks at its two paired leaves. -/
noncomputable def nativeCoupleUpperW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (p : SourcePair S) : Fin 2 → ℝ :=
  ![parentClockWith top τ (p.firstLeaf hS).toNode, parentClockWith top τ (p.secondLeaf hS).toNode]

theorem couple_parentClockWith {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) (p : SourcePair S)
    (a : GNode (nativeCoupleGarden D hS p).tree) :
    parentClockWith top τ ((nativeCoupleForest D hS p).nodeEmbedding a) =
      parentClockWith (nativeCoupleUpperW D hS top (nativeCoreClock D hS τ) p)
        (nativeCoupleClock D hS τ p) a := by
  have h := subforest_parentClockWith (nativeCoupleForest D hS p) top τ a
  have hr : (fun j => parentClockWith top τ ((nativeCoupleForest D hS p).root j)) =
      nativeCoupleUpperW D hS top (nativeCoreClock D hS τ) p := by
    funext j
    fin_cases j
    · exact parentClockWith_attachedNode D hS top τ (p.firstLeaf hS).toNode
    · exact parentClockWith_attachedNode D hS top τ (p.secondLeaf hS).toNode
  rw [hr] at h
  exact h

theorem fullTimeDomain_coreW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (top : Fin w → ℝ)
    (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomainW (fun b => layer b.toNode) top) :
    nativeCoreClock D hS τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) top := by
  intro b
  refine ⟨(hτ (D.coreBranch hS b)).1, (hτ (D.coreBranch hS b)).2.1,
    (hτ (D.coreBranch hS b)).2.2.1, ?_⟩
  have hd : (attachedNode D hS b.toNode).IsDesc (D.coreBranch hS b).toNode :=
    ⟨rfl, List.prefix_append _ _⟩
  have ht := branchTime_lt_parentClockWith_of_desc top τ (fun b => (hτ b).2.2.2)
    (attachedNode D hS b.toNode) (D.coreBranch hS b) hd
  exact lt_of_lt_of_eq ht (parentClockWith_attachedNode D hS top τ b.toNode)

theorem fullTimeDomain_coupleW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomainW (fun b => layer b.toNode) top) (p : SourcePair S) :
    nativeCoupleClock D hS τ p ∈ kDomain (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpperW D hS top (nativeCoreClock D hS τ) p q.1.1) 0 := by
  rw [kDomain_eq_edgeTimeDomain]
  intro q
  have hq := hτ (coupleContextBranch D hS p q)
  refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_, ?_⟩
  · have hc := (congrArg (parentClockWith top τ)
      (subforest_branch_node (nativeCoupleForest D hS p) q)).symm.trans
        (couple_parentClockWith D hS top τ p q.toNode)
    exact lt_of_lt_of_eq hq.2.2.2 hc
  · intro hl
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS)
        (nativeCoupleForest D hS p) (nativeCoupleForest_closed D hS p)
    exact (not_loneParent_of_plain _ hp q hl).elim

theorem fullTimeDomain_chainW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomainW (fun b => layer b.toNode) top) (b : GBranch S.tree) :
    nativeChainClock D hS τ b ∈ kDomain (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClockWith top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b) := by
  rw [kDomain_eq_edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
    (fun _ : Fin 1 => parentClockWith top (nativeCoreClock D hS τ) b.toNode)
    (nativeCoreClock D hS τ b)]
  have hcore := fullTimeDomain_coreW D hS layer top τ hτ b
  have hlower : ∀ q : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree,
      (decodedTree (D.tree b) (nodeSign S.sig b.1)).IsLoneParent q →
        nativeCoreClock D hS τ b < nativeChainClock D hS τ b q :=
    (pairedTree_lowerClock_iff (decodedTree_isPairedTree _ _)
      (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1))
      ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl) _ _ hcore.2.2.2 _).mpr
        (lt_of_lt_of_eq (hτ (D.coreBranch hS b)).2.2.2
          (core_parentClockWith_as_chain_lone D hS top τ b))
  intro q
  have hq := hτ (chainContextBranch D hS b ⟨q.1.2, q.2⟩)
  refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_, hlower q⟩
  exact lt_of_lt_of_eq hq.2.2.2 (chain_parentClockWith D hS top τ b q.toNode)

/-- TARGET redkg: the full source time domain is exactly the skeleton domain and the domains of its
actual inherited `K*_𝒬` and `K*_𝒯` kernels, for an exterior upper clock per root. -/
theorem timeDomain_reconstructionW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) :
    τ ∈ coreTimeDomainW (fun b => layer b.toNode) top ↔
      nativeCoreClock D hS τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) top ∧
      (∀ p : SourcePair S, nativeCoupleClock D hS τ p ∈
        kDomain (nativeCoupleLayered D hS layer hLayer p)
          (fun q => nativeCoupleUpperW D hS top (nativeCoreClock D hS τ) p q.1.1) 0) ∧
      (∀ b : GBranch S.tree, nativeChainClock D hS τ b ∈
        kDomain (nativeChainLayered D hS layer hLayer b)
          (fun _ => parentClockWith top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b)) := by
  constructor
  · intro h
    exact ⟨fullTimeDomain_coreW D hS layer top τ h,
      fullTimeDomain_coupleW D hS layer hLayer top τ h, fullTimeDomain_chainW D hS layer hLayer top τ h⟩
  · rintro ⟨hcore, hcouple, hchain⟩ c
    have hQ (p : SourcePair S) : nativeCoupleClock D hS τ p ∈
        edgeTimeDomain (nativeCoupleLayered D hS layer hLayer p)
          (nativeCoupleUpperW D hS top (nativeCoreClock D hS τ) p) 0 := by
      have h := hcouple p
      rw [kDomain_eq_edgeTimeDomain] at h
      exact h
    have hT (b : GBranch S.tree) : nativeChainClock D hS τ b ∈
        edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
          (fun _ => parentClockWith top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b) := by
      have h := hchain b
      rw [kDomain_eq_edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
        (fun _ : Fin 1 => parentClockWith top (nativeCoreClock D hS τ) b.toNode)
        (nativeCoreClock D hS τ b)] at h
      exact h
    obtain ⟨x, rfl⟩ := (sourceBranchEquiv D hS).surjective c
    rcases x with b | (⟨p, q⟩ | ⟨b, q⟩)
    · have hc := hcore b
      refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
      have hlower : nativeCoreClock D hS τ b <
          parentClock (parentClockWith top (nativeCoreClock D hS τ) b.toNode)
            (nativeChainClock D hS τ b) (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode :=
        (pairedTree_lowerClock_iff (decodedTree_isPairedTree _ _)
          (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1))
          ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl) _ _ hc.2.2.2 _).mp
            (fun q => (hT b q).2.2.2.2)
      exact lt_of_lt_of_eq hlower (core_parentClockWith_as_chain_lone D hS top τ b).symm
    · have hq := hQ p q
      refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_⟩
      have he := (congrArg (parentClockWith top τ)
        (subforest_branch_node (nativeCoupleForest D hS p) q)).symm.trans
          (couple_parentClockWith D hS top τ p q.toNode)
      exact lt_of_lt_of_eq hq.2.2.2.1 he.symm
    · let q' := chainBranchEquiv D b q
      have hq := hT b q'
      refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_⟩
      exact lt_of_lt_of_eq hq.2.2.2.1 (chain_parentClockWith D hS top τ b q'.toNode).symm

/-- The native domains of one replacement slot, for an exterior upper clock per root. -/
noncomputable def nativeDomainW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) : (s : ReplacementSlot S) → Set (NativeTimeBlock D s)
  | .inl p => kDomain (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
  | .inr b => kDomain (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClockWith tt τ b.toNode) (τ b)

/-- The skeleton factor of the full integrand, for an exterior upper clock per root. -/
noncomputable def coreKernelIntegrandW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ : ℂ) *
    (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
      (phaseProd L γ δ S (cosetDecoration S L k₀ κ)) τ

theorem nativeTimeDomain_reconstructionW {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (τ : GBranch (D.forest hS) → ℝ) :
    τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) 0 ↔
      nativeCoreClock D hS τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt ∧
        ∀ s : ReplacementSlot S, nativeTimeRestriction D hS τ s ∈
          nativeDomainW D hS layer hLayer tt (nativeCoreClock D hS τ) s := by
  rw [kDomain_eq_coreTimeDomainW (layeredReconstruction D hS layer hLayer) (D.garden_plain hS) tt 0]
  constructor
  · intro h
    obtain ⟨hc, hq, ht⟩ := (timeDomain_reconstructionW D hS layer hLayer tt τ).mp h
    refine ⟨hc, ?_⟩
    rintro (p | b)
    · exact hq p
    · exact ht b
  · rintro ⟨hc, hn⟩
    exact (timeDomain_reconstructionW D hS layer hLayer tt τ).mpr
      ⟨hc, fun p => hn (.inl p), fun b => hn (.inr b)⟩

end WaveTurbulence.RegRedLeaf
