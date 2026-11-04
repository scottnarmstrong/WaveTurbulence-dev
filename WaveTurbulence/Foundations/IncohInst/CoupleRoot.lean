/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleCarrier

/-! # Source finite root relation for the actual C2 couple carrier -/

public section
noncomputable section
open scoped Classical BigOperators
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 2} {Q : RegCpl}

/-- C2's signed positive-leaf relation gives exactly the analytic finite root certificate. -/
@[expose] def coupleRootInputCoordinates (hQ : Q.Decodes G) : RootInputCoordinates (coupleCarrier hQ) where
  sigma a := incohSigma G ((coupleInputEquiv G).symm a).1
  abs_sigma_le := by
    intro a
    have h := incohSigma_mem (G := G) ((coupleInputEquiv G).symm a).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h <;> rw [h] <;> norm_num
  root_row := by
    apply momentumRow_eq_of_eval
    intro u
    rw [map_sum, momentumRowEval_unit]
    simp only [map_zsmul]
    change (∑ a, incohSigma G ((coupleInputEquiv G).symm a).1 •
      momentumRowEval u (coupleNodeRow hQ ((coupleInputEquiv G).symm a).1.toNode)) = u none
    let κ : DecR G ℤ (u none) := decOfParams hQ (u none)
      (fun j => (u (some (j, 0)), u (some (j, 1))))
    have hev (a : GNode G.tree) : momentumRowEval u (coupleNodeRow hQ a) = κ.1 a :=
      coupleNodeRow_eval hQ a u
    simp only [hev]
    have he := root_eq_sigma_sum hQ.1 κ.2.1
    rw [κ.2.2 0, sum_plusLeaves] at he
    calc
      _ = ∑ ℓ : PlusLeaf G, incohSigma G ℓ.1 • κ.1 ℓ.1.toNode :=
        Equiv.sum_comp (coupleInputEquiv G).symm _
      _ = _ := he.symm

/-- Every source couple leaf carries an input; none is treated as a lone root leaf. -/
theorem coupleCarrier_all_leaves (hQ : Q.Decodes G) :
    ∀ i p, p ∈ ((coupleCarrier hQ).tree i).leaves → (coupleCarrier hQ).leafInput i p ≠ none := by
  intro i p hp
  change p ∈ (treeShape (G.tree i)).leaves at hp
  rw [treeShape_leaves] at hp
  simp only [coupleCarrier, dite_eq_left hp, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The source count is exactly `2n+1` input leaves, without any analytic assumption. -/
theorem coupleCarrier_input_count (hQ : Q.Decodes G) :
    Fintype.card (PlusLeaf G) = 2 * Q.links.length + 1 := by
  have h := card_plusLeaf hQ hQ.1
  simpa only [LinkCoord, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h

end WaveTurbulence.IncohInst
