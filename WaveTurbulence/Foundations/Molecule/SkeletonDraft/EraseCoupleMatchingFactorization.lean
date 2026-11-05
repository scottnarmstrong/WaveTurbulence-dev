/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleBackground
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleRootPairTriviality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCouplePairSite
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleIdentity

/-! # Exact complete matching factorization of one couple replacement slot -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_raw_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    let E := D.eraseCouple p
    (D.raw hS).pairs = ((E.raw hS).insertCouple
      (inflatedPosition S E.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S E.tree (p.secondLeaf hS).toNode) (D.couple p)).pairs := by
  classical
  let E := D.eraseCouple p
  let A := inflatedPosition S E.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S E.tree (p.secondLeaf hS).toNode
  by_cases hQ : D.couple p = .triv
  · have he : E = D := D.eraseCouple_eq_self p hQ
    have hi := (E.raw hS).insertCouple_triv A B (D.eraseCouple_pairSite hS p)
    rw [← hQ] at hi
    have hh := congrArg Raw.pairs hi
    exact (congrArg (fun F : ReconstructionData S => (F.raw hS).pairs) he).symm.trans hh.symm
  · have hn : (A,B) ∉ D.coupleBackground hS p := by
      intro hm
      apply hQ
      apply D.couple_eq_triv_of_root_pair_mem hS p
      change (A,B) ∈ D.attachmentPairs hS
      rw [D.attachmentPairs_eq_background_union hS p]
      exact Finset.mem_union_left _ hm
    have hb : E.couplePairBlock hS p = {(A,B)} := by
      change ((E.couple p).pairsAt A B).toFinset = _
      rw [D.eraseCouple_at]
      rfl
    have he : E.attachmentPairs hS = D.coupleBackground hS p ∪ {(A,B)} :=
      (E.attachmentPairs_eq_background_union hS p).trans
        (congrArg₂ (fun x y => x ∪ y) (D.eraseCouple_background hS p) hb)
    change D.attachmentPairs hS = (E.attachmentPairs hS).erase (A,B) ∪ D.couplePairBlock hS p
    rw [D.attachmentPairs_eq_background_union hS p,he]
    simp only [Finset.erase_union_distrib,Finset.erase_singleton,Finset.erase_eq_of_notMem hn,Finset.union_empty]

end WaveTurbulence.Reg.Skeleton
