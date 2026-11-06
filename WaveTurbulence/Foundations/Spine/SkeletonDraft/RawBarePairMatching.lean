/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairMatchingInner
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairMatchingRest

/-! # Full raw matching factorization for outer, inner and remaining bare-chain insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.insertChain_pair_matching {w : ℕ} (R : Raw w) (a : Address w)
    (m : MiniTreeCode) (X Y : RegChain) :
    ((((R.opB a m).insertChain (addrExt a [m.c]) X).insertChain
      (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])) Y).pairs) =
        (R.insertChain a (.pair m .triv .triv X Y)).pairs := by
  classical
  let b := addrExt a [m.c]
  let d := addrExt a ([m.c] ++ X.lonePath ++ [m.lone])
  let P := ((RegChain.pair m .triv .triv X .nil).pairsAt (nodeSign R.sig a) a).toFinset
  let F (p : Pair w) := (stretch b X.lonePath (relocate a m.c m.lone p.1),
    stretch b X.lonePath (relocate a m.c m.lone p.2))
  have hb : nodeSign R.sig b = slotSign (nodeSign R.sig a) m.c := nodeSign_step _ _ _
  have hd : nodeSign R.sig d = nodeSign R.sig a := by
    simp only [d,nodeSign_addrExt,Comb.pathSign_append,pathSign_singleton,lonePath_sign,slotSign_lone]
  have hfirst : ((R.opB a m).insertChain b X).pairs = R.pairs.image F ∪ P := by
    have hp := bare_pair_pairsAt_inner m X R.sig a
    change P = _ at hp
    simp only [Raw.insertChain,Raw.opB,Finset.image_union,Finset.image_image,Function.comp_def]
    rw [hb,Finset.union_assoc,← hp]
  have hfixed : P.image (fun p => (stretch d Y.lonePath p.1,stretch d Y.lonePath p.2)) = P := by
    calc
      _ = P.image id := Finset.image_congr (fun p hp =>
        bare_pair_initial_pairs_fixed_by_rest m X (nodeSign R.sig a) a p
          (List.mem_toFinset.mp hp) Y.lonePath)
      _ = P := Finset.image_id
  have hmap : (R.pairs.image F).image (fun p => (stretch d Y.lonePath p.1,stretch d Y.lonePath p.2)) =
      R.pairs.image (fun p => (stretch a (RegChain.pair m .triv .triv X Y).lonePath p.1,
        stretch a (RegChain.pair m .triv .triv X Y).lonePath p.2)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p _
    exact Prod.ext (stretch_outer_inner_rest a p.1 m.c m.lone X.lonePath Y.lonePath)
      (stretch_outer_inner_rest a p.2 m.c m.lone X.lonePath Y.lonePath)
  change (((R.opB a m).insertChain b X).insertChain d Y).pairs = _
  change (((R.opB a m).insertChain b X).pairs.image
    (fun p => (stretch d Y.lonePath p.1,stretch d Y.lonePath p.2)) ∪
      (Y.pairsAt (nodeSign R.sig d) d).toFinset) =
    R.pairs.image (fun p => (stretch a (RegChain.pair m .triv .triv X Y).lonePath p.1,
      stretch a (RegChain.pair m .triv .triv X Y).lonePath p.2)) ∪
      ((RegChain.pair m .triv .triv X Y).pairsAt (nodeSign R.sig a) a).toFinset
  rw [hfirst,Finset.image_union,hmap,hfixed,hd]
  rw [bare_pair_pairsAt_rest]
  exact Finset.union_assoc _ _ _

end WaveTurbulence.Reg.Skeleton
