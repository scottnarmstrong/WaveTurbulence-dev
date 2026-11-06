/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TreeContextInsertion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniContextContinuing
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairRestReplacement

/-! # Exact ordered forest factorization for bare chain pair insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.insertChain_pair_inner_forest {w : ℕ} (R : Raw w) (a : Address w)
    (ha : a.2 ∈ (R.tree a.1).nodes) (m : MiniTreeCode) (X : RegChain) :
    ((R.opB a m).insertChain (addrExt a [m.c]) X).tree =
      (R.insertChain a (.pair m .triv .triv X .nil)).tree := by
  let t := (R.tree a.1).subtreeAt a.2
  have h : Comb.subtree (R.tree a.1) a.2 = some t := by
    obtain ⟨u,hu⟩ := (Comb.subtree_exists_iff _ _).mpr ha
    exact hu.trans (congrArg some (subtreeAt_eq_of_subtree _ _ _ hu).symm)
  have hs : nodeSign R.sig (addrExt a [m.c]) = slotSign (nodeSign R.sig a) m.c := nodeSign_step _ _ _
  simp only [Raw.insertChain,Raw.opB,setAt_eq_replaceAt,addrExt,Function.update_self]
  change Function.update (Function.update R.tree a.1
    (Comb.replaceAt (R.tree a.1) a.2 (miniTreeContext m t))) a.1
      (Comb.replaceAt (Comb.replaceAt (R.tree a.1) a.2 (miniTreeContext m t)) (a.2 ++ [m.c])
        (X.plug (nodeSign R.sig (addrExt a [m.c]))
          ((Comb.replaceAt (R.tree a.1) a.2 (miniTreeContext m t)).subtreeAt (a.2 ++ [m.c])))) =
    Function.update R.tree a.1
      (Comb.replaceAt (R.tree a.1) a.2 ((RegChain.pair m .triv .triv X .nil).plug (nodeSign R.sig a) t))
  rw [insert_chain_under_frame h,Function.update_idem,hs,miniTreeContext_subtreeAt_continuing,
    bare_pair_plug_inner]

theorem Raw.insertChain_pair_forest {w : ℕ} (R : Raw w) (a : Address w)
    (ha : a.2 ∈ (R.tree a.1).nodes) (m : MiniTreeCode) (X Y : RegChain) :
    ((((R.opB a m).insertChain (addrExt a [m.c]) X).insertChain
      (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])) Y).tree) =
        (R.insertChain a (.pair m .triv .triv X Y)).tree := by
  let t := (R.tree a.1).subtreeAt a.2
  have h : Comb.subtree (R.tree a.1) a.2 = some t := by
    obtain ⟨u,hu⟩ := (Comb.subtree_exists_iff _ _).mpr ha
    exact hu.trans (congrArg some (subtreeAt_eq_of_subtree _ _ _ hu).symm)
  let d := addrExt a ([m.c] ++ X.lonePath ++ [m.lone])
  have hd : nodeSign R.sig d = nodeSign R.sig a := by
    simp only [d,nodeSign_addrExt,Comb.pathSign_append,pathSign_singleton,lonePath_sign,slotSign_lone]
  have hi := R.insertChain_pair_inner_forest a ha m X
  have ht : ((RegChain.pair m .triv .triv X .nil).plug (nodeSign R.sig a) t).subtreeAt
      ([m.c] ++ X.lonePath ++ [m.lone]) = t :=
    subtreeAt_eq_of_subtree _ _ _ (bare_pair_subtree_rest m X (nodeSign R.sig a) t)
  change Function.update ((R.opB a m).insertChain (addrExt a [m.c]) X).tree d.1
    ((((R.opB a m).insertChain (addrExt a [m.c]) X).tree d.1).setAt d.2
      (Y.plug (nodeSign R.sig d)
        ((((R.opB a m).insertChain (addrExt a [m.c]) X).tree d.1).subtreeAt d.2))) = _
  rw [hi]
  simp only [Raw.insertChain,setAt_eq_replaceAt,d,addrExt,Function.update_self]
  change Function.update (Function.update R.tree a.1
    (Comb.replaceAt (R.tree a.1) a.2 ((RegChain.pair m .triv .triv X .nil).plug (nodeSign R.sig a) t))) a.1
      (Comb.replaceAt (Comb.replaceAt (R.tree a.1) a.2
        ((RegChain.pair m .triv .triv X .nil).plug (nodeSign R.sig a) t))
        (a.2 ++ ([m.c] ++ X.lonePath ++ [m.lone]))
        (Y.plug (nodeSign R.sig d) ((Comb.replaceAt (R.tree a.1) a.2
          ((RegChain.pair m .triv .triv X .nil).plug (nodeSign R.sig a) t)).subtreeAt
          (a.2 ++ ([m.c] ++ X.lonePath ++ [m.lone]))))) =
      Function.update R.tree a.1 (Comb.replaceAt (R.tree a.1) a.2
        ((RegChain.pair m .triv .triv X Y).plug (nodeSign R.sig a) t))
  rw [insert_chain_under_frame h,Function.update_idem,hd,ht,bare_pair_plug_rest]

end WaveTurbulence.Reg.Skeleton
