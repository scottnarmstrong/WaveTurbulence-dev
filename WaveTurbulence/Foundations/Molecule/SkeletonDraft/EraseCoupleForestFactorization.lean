/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleMatchingFactorization
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleLeafSupport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawLeafSupportRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleSize
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionOrder

/-! # Exact ordered forest factorization of one couple replacement slot -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_raw {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    let E := D.eraseCouple p
    D.raw hS = (E.raw hS).insertCouple (inflatedPosition S E.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S E.tree (p.secondLeaf hS).toNode) (D.couple p) := by
  let E := D.eraseCouple p
  let A := inflatedPosition S E.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S E.tree (p.secondLeaf hS).toNode
  let T := (E.raw hS).insertCouple A B (D.couple p)
  have hsite : (E.raw hS).PairSite A B := D.eraseCouple_pairSite hS p
  have hp : (D.raw hS).pairs = T.pairs := D.eraseCouple_raw_pairs hS p
  have ho : (D.raw hS).order = T.order := by
    have ht := (E.raw hS).insertCouple_order A B hsite (D.couple p)
    have hd := D.forest_order hS
    have he := E.forest_order hS
    have hs := D.eraseCouple_size p
    change E.size + (D.couple p).size = D.size at hs
    change (D.raw hS).order = S.order + D.size at hd
    change (E.raw hS).order = S.order + E.size at he
    change T.order = (E.raw hS).order + (D.couple p).size at ht
    omega
  have hf := Raw.forest_eq_of_pairs_eq_order (D.raw hS) T (D.raw_valid hS) hp ho
    ((E.raw hS).insertCouple_pair_endpoints (E.raw_valid hS) A B hsite (D.couple p))
  exact Raw.ext (R := D.raw hS) (S := T) rfl hf hp

end WaveTurbulence.Reg.Skeleton
