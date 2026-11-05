/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SameTree

/-! # Order and per-tree layer counts for the collapsed LF unit

The same-tree hypothesis is geometric: designated source CL placements satisfy
it by `placement_same_tree`. It cannot be dropped for arbitrary placements.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w) (P : CorePlacement LG.garden)

theorem unitLayerTwist_order (he : SameLowerLayer LG P) :
    (unitLayerTwist LG P he).garden.order = LG.garden.order := by
  calc
    _ = Fintype.card (GBranch (unitTwistGarden LG.garden P).tree) := (Comb.card_gbranch _).symm
    _ = Fintype.card (GBranch LG.garden.tree) := Fintype.card_congr (coreBranchEquiv LG.garden P).symm
    _ = _ := Comb.card_gbranch _

/-- Literal layer counts in each original tree are preserved. -/
theorem unitLayerTwist_topOrder (he : SameLowerLayer LG P)
    (ht : P.lower.1.1 = (LG.garden.pair P.retained).1.1) (p : ℕ) (j : Fin w) :
    (unitLayerTwist LG P he).topOrder p j = LG.topOrder p j := by
  classical
  unfold LayeredGarden.topOrder
  apply Finset.card_bij (fun b _ => (coreBranchEquiv LG.garden P).symm b)
  · intro b hb
    obtain ⟨a,rfl⟩ := (coreBranchEquiv LG.garden P).surjective b
    simp only [Equiv.symm_apply_apply]
    have h := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨(coreBranchEquiv_tree_index P ht a).symm.trans h.1,
      (unitLayerTwist_branch LG P he a).symm.trans h.2⟩
  · intro a ha b hb hab
    exact (coreBranchEquiv LG.garden P).symm.injective hab
  · intro a ha
    refine ⟨coreBranchEquiv LG.garden P a, ?_, (coreBranchEquiv LG.garden P).symm_apply_apply a⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := (Finset.mem_filter.mp ha).2
    exact ⟨(coreBranchEquiv_tree_index P ht a).trans h.1,
      (unitLayerTwist_branch LG P he a).trans h.2⟩

/-- Once total order bounds all attached components, truncation tests only top trees. -/
theorem trunc_iff_topOrder (LG : LayeredGarden w) (p Ntop Natt : ℕ)
    (hn : LG.garden.order ≤ Natt) :
    LG.IsTrunc p Ntop Natt ↔ ∀ j, LG.topOrder p j ≤ Ntop := by
  exact ⟨And.left, fun h => ⟨h, fun u _ => (LG.attachedOrder_le_order p u).trans hn⟩⟩

/-- The collapsed unit preserves the full truncation predicate whenever the
attached-component bound dominates the total order. -/
theorem unitLayerTwist_isTrunc (he : SameLowerLayer LG P)
    (ht : P.lower.1.1 = (LG.garden.pair P.retained).1.1)
    (p Ntop Natt : ℕ) (hn : LG.garden.order ≤ Natt) :
    (unitLayerTwist LG P he).IsTrunc p Ntop Natt ↔ LG.IsTrunc p Ntop Natt := by
  rw [trunc_iff_topOrder _ _ _ _ ((unitLayerTwist_order LG P he).trans_le hn),
    trunc_iff_topOrder _ _ _ _ hn]
  simp only [unitLayerTwist_topOrder LG P he ht]

end WaveTurbulence.LFTwist
