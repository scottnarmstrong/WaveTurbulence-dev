/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentityRaw

/-! # Exact pair formula for couple-only replacements at actual canonical source pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem inflatedPosition_eq_self_of_nil {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (hX : ∀ b, X b = .nil) (a : GNode S.tree) : inflatedPosition S X a = a.1 := by
  have he : X = (ReconstructionData.identity S).tree := funext hX
  exact (congrArg (fun X => inflatedPosition S X a) he).trans (inflatedPosition_identity S a)

theorem ReconstructionData.attachmentPairs_of_nil_tree {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hD : ∀ b, D.tree b = .nil) :
    D.attachmentPairs hS = Finset.univ.biUnion (fun p : SourcePair S =>
      ((D.couple p).pairsAt p.1.1 p.1.2).toFinset) := by
  classical
  have hp (a : GNode S.tree) : inflatedPosition S D.tree a = a.1 := inflatedPosition_eq_self_of_nil S D.tree hD a
  have he : (Finset.univ.biUnion (fun _ : GBranch S.tree => (∅ : Finset (Pair w)))) = ∅ := by
    ext q
    simp
  simp only [ReconstructionData.attachmentPairs,hD,hp,RegChain.pairsAt,List.toFinset_nil,he,Finset.union_empty]
  rfl

end WaveTurbulence.Reg.Skeleton
