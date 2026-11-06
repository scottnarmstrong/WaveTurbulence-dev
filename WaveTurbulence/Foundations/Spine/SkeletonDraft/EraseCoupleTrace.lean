/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleCollapseDecodes
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularSubcoupleCollapseTrace
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DecodedCoreEmbedding

/-! # Actual erasure of a regular couple slot with every original core branch retained in place -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_trace {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) (p : SourcePair S) :
    ∃ H : Garden w, (D.eraseCouple p).Decodes hS H ∧
      ∃ T : ReductionTrace G H, ∀ c : GBranch H.tree, (T.branches c).1 = c.1 := by
  by_cases hQ : D.couple p = .triv
  · have he := D.eraseCouple_eq_self p hQ
    exact ⟨G,he.symm ▸ hd,ReductionTrace.refl G,fun _ => rfl⟩
  · let h := D.decoded_couple_isSubCouple hS hd p
    obtain ⟨T,hT⟩ := regular_subcouple_collapse_trace G hd.1 h (D.decoded_couple_regular hS hd p)
    refine ⟨collapseCoupleGarden h,D.eraseCouple_collapse_decodes hS hd p hQ,T,?_⟩
    intro c
    rw [hT]
    rfl

end WaveTurbulence.Reg.Skeleton
