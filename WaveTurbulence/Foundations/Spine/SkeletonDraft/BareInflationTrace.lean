/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EraseBareTreeTrace
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeCoreTransport
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EraseTreeSize
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionIdentityCore

/-! # Actual erasure of every bare branch context with the original core retained exactly -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.bareInflation_trace {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hD : D.IsBareInflation)
    (G : Garden w) (hd : D.Decodes hS G) :
    ∃ T : ReductionTrace G S, ∀ b : GBranch S.tree, (T.branches b).1 = D.corePosition b := by
  classical
  generalize hsize : D.size = N
  induction N using Nat.strong_induction_on generalizing D G with
  | h N ih =>
    by_cases hnil : ∀ b, D.tree b = .nil
    · have hidentity := D.eq_identity_of_nil_triv hnil hD.2
      subst D
      have hg : G = S := rawOfGarden_injective_plain hd.1 hS
        (hd.2.symm.trans (ReconstructionData.identity_raw S hS))
      subst G
      exact ⟨ReductionTrace.refl S,fun b => (ReconstructionData.identity_corePosition S b).symm⟩
    · obtain ⟨b,hb⟩ := not_forall.mp hnil
      let E := D.eraseTree b
      have hpos : 0 < (D.tree b).size := by
        by_contra hn
        have hz : (D.tree b).size = 0 := by omega
        exact hb (eq_nil_of_size_zero _ hz)
      have heSize := D.eraseTree_size b
      change E.size + (D.tree b).size = D.size at heSize
      have hsmall : E.size < N := by omega
      obtain ⟨H,hE,T,hT⟩ := D.eraseBareTree_trace hS hd b (hD.1 b)
      obtain ⟨U,hU⟩ := ih E.size hsmall E (hD.eraseTree b) H hE rfl
      refine ⟨ReductionTrace.trans T U,?_⟩
      intro c
      change (T.branches (U.branches c)).1 = _
      rw [hT,hU]
      exact (D.eraseTree_corePosition b c).symm

end WaveTurbulence.Reg.Skeleton
