/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CrownLookup

/-! # The switched source crown inflates to the switched actual crown

The erased lower regular tree is nil, so its flipped root sign has no context
to change. Every proper child subtree uses the proved local raw covariance.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links

private theorem inflateTreeAt_node_eq {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (l m r : TTree) (a : Address w) :
    inflateTreeAt σ X Y (.node l m r) a = (X a).plug (nodeSign σ a)
      (.node (inflateTreeAt σ X Y l (addrExt a [0])) (inflateTreeAt σ X Y m (addrExt a [1]))
        (inflateTreeAt σ X Y r (addrExt a [2]))) := rfl

/-- The lower-root switch commutes with all ordinary regular replacements. -/
theorem crown_inflation_twist {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain)
    (D : ReconstructionData S) (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    inflateTreeAt (unitTwistGarden S P).sig (branchLookup (twistReconstruction S P hS D))
      (leafLookup (twistReconstruction S P hS D) (unitTwistGarden_plain S P hS))
      (switchFree P.keep (lowerCrown S P.lower)) (S.pair P.retained).1 =
    switchFree P.keep (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS)
      (lowerCrown S P.lower) P.lower.1) := by
  let newD := twistReconstruction S P hS D
  let newY := leafLookup newD (unitTwistGarden_plain S P hS)
  let f := exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep
  have hold : branchLookup D P.lower.1 = .nil := (branchLookup_branch D P.lower).trans hnil
  have hnew : branchLookup newD (S.pair P.retained).1 = .nil :=
    (congrArg (branchLookup newD) (coreBranchEquiv_lower_val S P).symm).trans
      ((branchLookup_twist S P hS D P.lower).trans hnil)
  cases ht : lowerCrown S P.lower with
  | leaf =>
    have hh := lowerCrown_root_not_leaf S P
    rw [ht] at hh
    exact (hh (Finset.mem_singleton_self [])).elim
  | node l m r =>
    have hchild (i : Fin 3) :
        inflateTreeAt (unitTwistGarden S P).sig (branchLookup newD) newY (![l,m,r] i)
          (addrExt (S.pair P.retained).1 [freeSwap P.keep i]) =
        inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (![l,m,r] i) (addrExt P.lower.1 [i]) := by
      have hf := exchange_respectsAt_lower_child P.lower.1 (S.pair P.retained).1 P.keep i
      have hx (q : Path) (hq' : q ∈ (![l,m,r] i).branching) :
          branchLookup newD (f (addrExt (addrExt P.lower.1 [i]) q)) =
            branchLookup D (addrExt (addrExt P.lower.1 [i]) q) := by
        have hc : i :: q ∈ (lowerCrown S P.lower).branching := by
          rw [ht]
          exact (cons_mem_branching_node l m r i q).mpr hq'
        have hh := branchLookup_exchange S P hS D
          ⟨addrExt P.lower.1 (i :: q),crown_branch_mem S P (i :: q) hc⟩
        change branchLookup newD (f (addrExt P.lower.1 (i :: q))) =
          branchLookup D (addrExt P.lower.1 (i :: q)) at hh
        rw [addrExt_cons P.lower.1 i q] at hh
        exact hh
      have hy (q : Path) (hq' : q ∈ (![l,m,r] i).leaves) :
          newY (f (addrExt (addrExt P.lower.1 [i]) q)) = leafLookup D hS (addrExt (addrExt P.lower.1 [i]) q) := by
        have hc : i :: q ∈ (lowerCrown S P.lower).leaves := by
          rw [ht]
          exact (cons_mem_leaves_node l m r i q).mpr hq'
        have hh := leafLookup_exchange S P hS D hq
          ⟨addrExt P.lower.1 (i :: q),crown_leaf_mem S P (i :: q) hc⟩
        change newY (f (addrExt P.lower.1 (i :: q))) = leafLookup D hS (addrExt P.lower.1 (i :: q)) at hh
        rw [addrExt_cons P.lower.1 i q] at hh
        exact hh
      have hs (q : Path) (hq' : q ∈ (![l,m,r] i).branching) :
          nodeSign (unitTwistGarden S P).sig (f (addrExt (addrExt P.lower.1 [i]) q)) =
            nodeSign S.sig (addrExt (addrExt P.lower.1 [i]) q) := by
        have hc : i :: q ∈ (lowerCrown S P.lower).branching := by
          rw [ht]
          exact (cons_mem_branching_node l m r i q).mpr hq'
        have hh := crown_nonroot_branch_sign S P (i :: q) hc (List.cons_ne_nil _ _)
        rw [addrExt_cons P.lower.1 i q] at hh
        exact hh
      have hh := inflateTreeAt_map S.sig (unitTwistGarden S P).sig (branchLookup D) (leafLookup D hS)
        (branchLookup newD) newY f (![l,m,r] i) (addrExt P.lower.1 [i]) hf hx hy hs
      exact (congrArg (inflateTreeAt (unitTwistGarden S P).sig (branchLookup newD) newY (![l,m,r] i))
        (exchange_lower_child_root P.lower.1 (S.pair P.retained).1 P.keep i).symm).trans hh
    have hcrown : inflateTreeAt (unitTwistGarden S P).sig (branchLookup newD) newY
        (switchFree P.keep (.node l m r)) (S.pair P.retained).1 =
      switchFree P.keep (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (.node l m r) P.lower.1) := by
      have hk : P.keep = 0 ∨ P.keep = 2 := by have := P.outer; omega
      rcases hk with hk | hk
      · have h0 := hchild 0
        have h1 := hchild 1
        have h2 := hchild 2
        simp [hk, freeSwap, Equiv.swap_apply_def] at h0 h1 h2
        simp only [switchFree, hk, ite_true, inflateTreeAt_node_eq, hold, hnew, RegChain.plug]
        congr 1
      · have h0 := hchild 0
        have h1 := hchild 1
        have h2 := hchild 2
        simp [hk, freeSwap, Equiv.swap_apply_def] at h0 h1 h2
        simp only [switchFree, hk, show (2 : Fin 3) ≠ 0 by decide, ite_false, inflateTreeAt_node_eq, hold, hnew, RegChain.plug]
        congr 1
    simpa only [ht] using hcrown

end WaveTurbulence.LFTwist
