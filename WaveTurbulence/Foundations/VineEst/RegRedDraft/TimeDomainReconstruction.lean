/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeTimeDomainForward

/-! # Exact time-domain decomposition in TARGET regred -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

/-- TARGET redkg: the full source time domain is exactly the skeleton domain
and the domains of its actual inherited KQstar and KTstar kernels. The skeleton
is only pre-layered; no matching-layer condition on its old leaves is imposed. -/
theorem timeDomain_reconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) :
    τ ∈ coreTimeDomain (fun b => layer b.toNode) top ↔
      nativeCoreClock D hS τ ∈ coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top ∧
      (∀ p : SourcePair S, nativeCoupleClock D hS τ p ∈
        kDomain (nativeCoupleLayered D hS layer hLayer p)
          (fun q => nativeCoupleUpper D hS top (nativeCoreClock D hS τ) p q.1.1) 0) ∧
      (∀ b : GBranch S.tree, nativeChainClock D hS τ b ∈
        kDomain (nativeChainLayered D hS layer hLayer b)
          (fun _ => parentClock top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b)) := by
  constructor
  · intro h
    exact ⟨fullTimeDomain_core D hS layer top τ h,
      fullTimeDomain_couple D hS layer hLayer top τ h,fullTimeDomain_chain D hS layer hLayer top τ h⟩
  · rintro ⟨hcore,hcouple,hchain⟩ c
    have hQ (p : SourcePair S) : nativeCoupleClock D hS τ p ∈
        edgeTimeDomain (nativeCoupleLayered D hS layer hLayer p)
          (nativeCoupleUpper D hS top (nativeCoreClock D hS τ) p) 0 := by
      have h := hcouple p
      rw [kDomain_eq_edgeTimeDomain] at h
      exact h
    have hT (b : GBranch S.tree) : nativeChainClock D hS τ b ∈
        edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
          (fun _ => parentClock top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b) := by
      have h := hchain b
      rw [kDomain_eq_edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
        (fun _ : Fin 1 => parentClock top (nativeCoreClock D hS τ) b.toNode)
        (nativeCoreClock D hS τ b)] at h
      exact h
    obtain ⟨x,rfl⟩ := (sourceBranchEquiv D hS).surjective c
    rcases x with b | (⟨p,q⟩ | ⟨b,q⟩)
    · have hc := hcore b
      refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
      have hlower : nativeCoreClock D hS τ b <
          parentClock (parentClock top (nativeCoreClock D hS τ) b.toNode)
            (nativeChainClock D hS τ b) (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode :=
        (pairedTree_lowerClock_iff (decodedTree_isPairedTree _ _)
          (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1))
          ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl) _ _ hc.2.2.2 _).mp
            (fun q => (hT b q).2.2.2.2)
      exact lt_of_lt_of_eq hlower (core_parentClock_as_chain_lone D hS top τ b).symm
    · have hq := hQ p q
      refine ⟨hq.1,hq.2.1,hq.2.2.1,?_⟩
      have he := (congrArg (parentClock top τ)
        (subforest_branch_node (nativeCoupleForest D hS p) q)).symm.trans
          (couple_parentClock D hS top τ p q.toNode)
      exact lt_of_lt_of_eq hq.2.2.2.1 he.symm
    · let q' := chainBranchEquiv D b q
      have hq := hT b q'
      refine ⟨hq.1,hq.2.1,hq.2.2.1,?_⟩
      exact lt_of_lt_of_eq hq.2.2.2.1 (chain_parentClock D hS top τ b q'.toNode).symm

end WaveTurbulence.RegRed
