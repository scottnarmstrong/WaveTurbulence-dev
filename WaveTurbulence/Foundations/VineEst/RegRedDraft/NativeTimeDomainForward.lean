/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeClockTransport

/-! # Restricting the full source time domain to the actual native kernels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem fullTimeDomain_couple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomain (fun b => layer b.toNode) top) (p : SourcePair S) :
    nativeCoupleClock D hS τ p ∈ kDomain (nativeCoupleLayered D hS layer hLayer p)
      (fun q => nativeCoupleUpper D hS top (nativeCoreClock D hS τ) p q.1.1) 0 := by
  rw [kDomain_eq_edgeTimeDomain]
  intro q
  have hq := hτ (coupleContextBranch D hS p q)
  refine ⟨hq.1,hq.2.1,hq.2.2.1,?_,?_⟩
  · have hc := (congrArg (parentClock top τ)
      (subforest_branch_node (nativeCoupleForest D hS p) q)).symm.trans
        (couple_parentClock D hS top τ p q.toNode)
    exact lt_of_lt_of_eq hq.2.2.2 hc
  · intro hl
    have hp : (nativeCoupleLayered D hS layer hLayer p).garden.IsPlain :=
      Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS)
        (nativeCoupleForest D hS p) (nativeCoupleForest_closed D hS p)
    exact (not_loneParent_of_plain _ hp q hl).elim

theorem fullTimeDomain_chain {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : τ ∈ coreTimeDomain (fun b => layer b.toNode) top) (b : GBranch S.tree) :
    nativeChainClock D hS τ b ∈ kDomain (nativeChainLayered D hS layer hLayer b)
      (fun _ => parentClock top (nativeCoreClock D hS τ) b.toNode) (nativeCoreClock D hS τ b) := by
  rw [kDomain_eq_edgeTimeDomain (nativeChainLayered D hS layer hLayer b)
    (fun _ : Fin 1 => parentClock top (nativeCoreClock D hS τ) b.toNode)
    (nativeCoreClock D hS τ b)]
  have hcore := fullTimeDomain_core D hS layer top τ hτ b
  have hlower : ∀ q : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree,
      (decodedTree (D.tree b) (nodeSign S.sig b.1)).IsLoneParent q →
        nativeCoreClock D hS τ b < nativeChainClock D hS τ b q :=
    (pairedTree_lowerClock_iff (decodedTree_isPairedTree _ _)
      (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1))
      ((decodesTree_lone_iff (decodedTree_decodes _ _) _).mpr rfl) _ _ hcore.2.2.2 _).mpr
        (lt_of_lt_of_eq (hτ (D.coreBranch hS b)).2.2.2 (core_parentClock_as_chain_lone D hS top τ b))
  intro q
  have hq := hτ (chainContextBranch D hS b ⟨q.1.2,q.2⟩)
  refine ⟨hq.1,hq.2.1,hq.2.2.1,?_,hlower q⟩
  exact lt_of_lt_of_eq hq.2.2.2 (chain_parentClock D hS top τ b q.toNode)

end WaveTurbulence.RegRed
