/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Complete valid matching endpoints determine the literal ordered forest -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.tree_eq_of_valid_pairs {w : ℕ} (R T : Raw w) (hR : R.Valid) (hT : T.Valid)
    (hp : R.pairs = T.pairs) : R.tree = T.tree := by
  apply forest_eq_of_leaf_set_eq
  ext z
  have forward (A B : Raw w) (hA : A.Valid) (hB : B.Valid) (hp : A.pairs = B.pairs)
      (hz : z ∈ forestSet A.tree TTree.leaves) : z ∈ forestSet B.tree TTree.leaves := by
    have hl := (mem_forestSet _).mp hz
    obtain ⟨p,hm,_⟩ := hA.2 ⟨z,hl⟩
    have hv := hB.1 p (hp ▸ hm.1)
    apply (mem_forestSet _).mpr
    rcases hm.2 with he | he
    · exact (congrArg (fun z : Address w => z.2 ∈ (B.tree z.1).leaves) he).mp hv.1
    · exact (congrArg (fun z : Address w => z.2 ∈ (B.tree z.1).leaves) he).mp hv.2.1
  exact ⟨forward R T hR hT hp,forward T R hT hR hp.symm⟩

theorem Raw.eq_of_valid_sig_pairs {w : ℕ} (R T : Raw w) (hR : R.Valid) (hT : T.Valid)
    (hs : R.sig = T.sig) (hp : R.pairs = T.pairs) : R = T :=
  Raw.ext hs (R.tree_eq_of_valid_pairs T hR hT hp) hp

end WaveTurbulence.Reg.Skeleton
