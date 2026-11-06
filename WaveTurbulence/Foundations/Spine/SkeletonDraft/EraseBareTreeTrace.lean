/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeRawFactorization
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BareChainErasureTrace
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSubtrees

/-! # Actual erasure trace for one bare tree replacement in a decoded reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseBareTree_trace {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
    (b : GBranch S.tree) (hb : BareChain (D.tree b)) :
    ∃ H : Garden w, (D.eraseTree b).Decodes hS H ∧
      ∃ T : ReductionTrace G H, ∀ c : GBranch H.tree,
        (T.branches c).1 =
          stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath c.1 := by
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have ha : A.2 ∈ ((E.raw hS).tree A.1).nodes :=
    (Comb.subtree_exists_iff _ _).mp ⟨_,E.forest_subtree_position hS b.toNode⟩
  obtain ⟨H,hH,he,T,hT⟩ := bareChain_erasure_trace (D.tree b) hb (E.raw hS) A ha G hd.1
    (hd.2.symm.trans (D.eraseTree_raw hS b))
  exact ⟨H,⟨hH,he.symm⟩,T,hT⟩

end WaveTurbulence.Reg.Skeleton
