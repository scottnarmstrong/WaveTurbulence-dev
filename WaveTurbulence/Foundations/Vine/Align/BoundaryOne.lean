/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.NodeTrace
public import WaveTurbulence.Foundations.Vine.B.Src2
/-! The excluded boundary child has its original ordered port after splicing. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineA VineB RedSplice TTree Twist Mole
variable {w : ℕ} {S : Garden w}

/-- B1b (Mk-general form of `stShape_hmom_one`). -/
theorem stShape_hmom_oneMk (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length) :
    (stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 1 =
      ((stShape (Mk := Mk) hM σ).hinge (unitBlkMk_disj (Mk := Mk) hM σ) j).child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).excluded := by
  let Φ := stShape (Mk := Mk) hM σ
  let hd := unitBlkMk_disj (Mk := Mk) hM σ
  let n := Φ.hmom hd j 1
  let c := Φ.hinge hd j
  let u := unitBlkMk (Mk := Mk) hM σ j
  have he : spliceOldNode (unitBlocks (Mk := Mk) S σ) n = u.upper.child (regionOf u).excluded :=
    (stShape_node_eqMk (Mk := Mk) hM σ n).symm.trans (Φ.node_hmom hd j 1)
  have ho : (spliceOldNode (unitBlocks (Mk := Mk) S σ) n).1.2 ≠ [] := by
    rw [he]
    exact VineB.child_nonroot _ _
  have hn : n.1.2 ≠ [] := fun h => ho ((spliceOldNode_root _ n).mpr h)
  have hp : GNode.parent (spliceOldNode (unitBlocks (Mk := Mk) S σ) n) ho = u.upper := by
    exact (spliceNodeParent_congr ho (VineB.child_nonroot _ _) he).trans (VineB.parent_child _ _ _)
  have hf : repC (stSt (Mk := Mk) S σ).cls u.upper = u.upper := by
    rw [← Φ.br_hinge hd j]
    exact splice_old_branch_fixed _ c
  have hc : GNode.parent n hn = c := by
    apply Φ.br_inj
    exact ((spliceOldNode_parent _ n hn ho).trans
      ((congrArg (repC (spliceFold S (unitBlocks (Mk := Mk) S σ)).cls) hp).trans hf)).trans (Φ.br_hinge hd j).symm
  have hk : n.1.2.getLast hn = (regionOf u).excluded := by
    have ht := spliceOldNode_port (unitBlocks (Mk := Mk) S σ) n hn ho (by rw [hp]; exact hf)
    exact ht.trans (node_last_of_eq_child _ ho _ _ he)
  exact (parent_child_eq_node n hn).symm.trans (by rw [hc, hk])

/-- The upper external boundary node sits at the original excluded child slot. -/
theorem stShape_hmom_one (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (j : Fin (unitBlocks S σ).length) :
    (stShape hM σ).hmom (unitBlk_disj hM σ) j 1 =
      ((stShape hM σ).hinge (unitBlk_disj hM σ) j).child (regionOf (unitBlk hM σ j)).excluded := stShape_hmom_oneMk (Mk := ∅) hM σ j

end WaveTurbulence.VineAlign
