/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EraseCoupleTrace
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleSize
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataExt

/-! # Native simultaneous erasure of all original leaf-pair replacement couples -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Retain every regular tree context and replace every original couple slot by a pair of leaves. -/
noncomputable def ReconstructionData.eraseAllCouples {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) : ReconstructionData S where
  tree := D.tree
  couple := fun _ => .triv
  tree_wf := D.tree_wf
  couple_wf := fun _ => rfl

theorem ReconstructionData.eraseCouple_eraseAllCouples {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (p : SourcePair S) :
    (D.eraseCouple p).eraseAllCouples = D.eraseAllCouples :=
  ReconstructionData.ext_tree_couple _ _ rfl rfl

theorem ReconstructionData.eraseAllCouples_trace {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (G : Garden w) (hd : D.Decodes hS G) :
    ∃ H : Garden w, D.eraseAllCouples.Decodes hS H ∧
      ∃ T : ReductionTrace G H, ∀ c : GBranch H.tree, (T.branches c).1 = c.1 := by
  classical
  generalize hsize : D.size = N
  induction N using Nat.strong_induction_on generalizing D G with
  | h N ih =>
    by_cases htriv : ∀ p, D.couple p = .triv
    · have he : D.eraseAllCouples = D := ReconstructionData.ext_tree_couple _ _ rfl (funext (fun p => (htriv p).symm))
      exact ⟨G,he.symm ▸ hd,ReductionTrace.refl G,fun _ => rfl⟩
    · obtain ⟨p,hp⟩ := not_forall.mp htriv
      let E := D.eraseCouple p
      have hpos : 0 < (D.couple p).size := by
        by_contra hn
        exact hp (eq_triv_of_wf_size_zero _ (D.couple_wf p) (by omega))
      have hsz := D.eraseCouple_size p
      change E.size + (D.couple p).size = D.size at hsz
      have hsmall : E.size < N := by omega
      obtain ⟨H,hH,T,hT⟩ := D.eraseCouple_trace hS hd p
      obtain ⟨K,hK,U,hU⟩ := ih E.size hsmall E H hH rfl
      refine ⟨K,(D.eraseCouple_eraseAllCouples p) ▸ hK,ReductionTrace.trans T U,?_⟩
      intro c
      change (T.branches (U.branches c)).1 = _
      exact (hT _).trans (hU c)

end WaveTurbulence.Reg.Skeleton
