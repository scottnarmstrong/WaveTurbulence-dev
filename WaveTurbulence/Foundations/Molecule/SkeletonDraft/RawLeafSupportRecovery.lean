/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Leaf coverage and exact order recover a forest from matching endpoint support -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.forest_eq_of_pairs_eq_order {w : ℕ} (R T : Raw w) (hR : R.Valid)
    (hp : R.pairs = T.pairs) (ho : R.order = T.order)
    (ht : ∀ p ∈ T.pairs, p.1.2 ∈ (T.tree p.1.1).leaves ∧ p.2.2 ∈ (T.tree p.2.1).leaves) :
    R.tree = T.tree := by
  classical
  apply forest_eq_of_leaf_set_eq
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    have hl : z.2 ∈ (R.tree z.1).leaves := (mem_forestSet _).mp hz
    obtain ⟨p,hpR,_⟩ := hR.2 ⟨z,hl⟩
    have hpT : p ∈ T.pairs := hp ▸ hpR.1
    have hv := ht p hpT
    apply (mem_forestSet _).mpr
    rcases hpR.2 with he | he
    · have hh := congrArg (fun z : Address w => z.2 ∈ (T.tree z.1).leaves) he
      exact hh.mp hv.1
    · have hh := congrArg (fun z : Address w => z.2 ∈ (T.tree z.1).leaves) he
      exact hh.mp hv.2
  · rw [forest_leaf_set_card,forest_leaf_set_card]
    change 2 * T.order + w ≤ 2 * R.order + w
    omega

end WaveTurbulence.Reg.Skeleton
