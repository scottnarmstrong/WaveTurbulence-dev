/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitDec
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.LocalSlotBoundarySum
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp3State

/-! # P4-W2 (b1): the momentum relation at the lower joint of a split

* `cl_boundary_momentum_loc`: `RegRed.cl_boundary_momentum` for LOCAL decorations: only the conservation at the branches of the block `S` and the matching
  of the internal leaves of `S` are used (`sum_slotSum_eq_externalSlots_local`), so it applies to `clExtendIndices` of a local decoration of any region
  containing `S`.
* `split_gap_lattice`: for a split `S ∪ T` at the lower joint `b = sb.b` of the piece, `σ_b (x_b - x_{kept}) = x_{b'.pos} - x_{b'.neg}` (lattice values), where
  `b'` is the lower joint of the lower block `T` (= the bottom of the chain) and `kept = sp.RS.kept` is the retained leaf's child slot at `b`.  Together with the
  gap of the whole region this gives `low - ret = ± (E₀ - E₁)` (finding 3 of the FINAL export).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.RegRed TTree

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **`cl_boundary_momentum` for local decorations** (conservation on the branches of `S` and matching of the internal leaves only). -/
theorem cl_boundary_momentum_loc (hB : G.molecule.IsBlock S a b) (D : CLRegionData G S a b)
    (k : GNode G.tree → Mom d)
    (hc : ∀ v ∈ S, k v.toNode = k (v.child 0) - k (v.child 1) + k (v.child 2))
    (hk : ∀ ℓ, Mole.IsInternalLeaf G S ℓ → k ℓ.toNode = k (G.pair ℓ).toNode) :
    ((G.sign a.toNode : ℤ) : ℝ) • (k a.toNode - k (a.child D.excluded)) =
      k (b.child D.positive) - k (b.child D.negative) := by
  have he : (∑ v ∈ S, Mole.slotSum G k v) = ((G.sign a.toNode : ℤ) : ℝ) • k a.toNode -
        ((G.sign (a.child D.excluded) : ℤ) : ℝ) • k (a.child D.excluded) -
        ((G.sign (b.child D.positive) : ℤ) : ℝ) • k (b.child D.positive) -
        ((G.sign (b.child D.negative) : ℤ) : ℝ) • k (b.child D.negative) := by
    rw [sum_slotSum_eq_externalSlots_local G S k hk, cl_sum_externalSlotSum hB k,
      cl_externalSlotSum_upper hB D k, cl_externalSlotSum_lower hB D k,
      slotWeight_parent, slotWeight_child, slotWeight_child, slotWeight_child]
    simp only [neg_smul]
    abel
  have h0 : (∑ v ∈ S, Mole.slotSum G k v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact (Mole.slotSum_eq_zero_iff G k v).mpr (hc v hv)
  rw [h0, Mole.outer_child_sign G a D.excluded D.excluded_ne_middle, D.positive_sign, D.negative_sign] at he
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_smul, neg_smul, sub_neg_eq_add] at he
  apply sub_eq_zero.mp
  have ht : ((G.sign a.toNode : ℤ) : ℝ) • k a.toNode -
      ((G.sign a.toNode : ℤ) : ℝ) • k (a.child D.excluded) - k (b.child D.positive) + k (b.child D.negative) =
      ((G.sign a.toNode : ℤ) : ℝ) • (k a.toNode - k (a.child D.excluded)) -
        (k (b.child D.positive) - k (b.child D.negative)) := by rw [smul_sub]; abel
  exact ht.symm.trans he.symm

open WaveTurbulence.VineEstS4 WaveTurbulence.Links WaveTurbulence.Twist in
/-- **The signed gap at the lower joint of a split**: `σ_b (k_b - k_{kept}) = k_{pos} - k_{neg}` (lattice form, local decoration). -/
theorem split_gap_lattice {S : Garden w} {ι : Type*} {F : CoreFamily S ι} {pstar : ι} {J : Set ι}
    (sp : SplitAt S F pstar J) (L : ℝ) (x : GNode S.tree → (Fin d → ℤ))
    (hc : ∀ v ∈ sp.tb.U, x v.toNode = x (v.child 0) - x (v.child 1) + x (v.child 2))
    (hl : ∀ ℓ, Mole.IsInternalLeaf S sp.tb.U ℓ → x ℓ.toNode = x (S.pair ℓ).toNode) :
    ((S.sign sp.sb.b.toNode : ℤ) : ℝ) •
        (latticePoint L (x sp.sb.b.toNode) - latticePoint L (x (sp.sb.b.child sp.RS.kept))) =
      latticePoint L (x (sp.tb.b.child sp.RT.positive)) - latticePoint L (x (sp.tb.b.child sp.RT.negative)) := by
  have h := cl_boundary_momentum_loc (d := d) sp.hT sp.RT (fun y => latticePoint L (x y))
    (fun v hv => by simp only [hc v hv, latticePoint_add, latticePoint_sub])
    (fun ℓ hℓ => by simp only [hl ℓ hℓ])
  rw [split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT] at h
  exact h

end WaveTurbulence.VineEstS5C.P4.W2
