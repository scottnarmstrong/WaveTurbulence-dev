/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Src3
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintBoundaryNormalization
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint
import Mathlib.Tactic

/-!
# VINE-B Part II (4): the `outSet` clauses of G2 that follow from the hinge decoration

For a decoration `z` of `G_sb`, the unit momenta `β i = base + latticePoint L (z (hmom j i))` lie in the coset, and
`sumintBoundary ζ β` satisfies `v 0 - v 1 = v 3 - v 2` (signed conservation at the hinge) and is within `1` of
`sumintBoundary ζ centre` when `β` is within `1` of `centre`.  The remaining clause of `outSet` (the SG gap
`v 0 ≠ v 1`, `‖v 0 - v 1‖ ≤ L^(-γ+η)`) is `UnitGap` on `β`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The SG gap clause of `outSet`, in the physical (unpermuted) boundary momenta `β = (k_{u1}, k_{u11}, k_{u21}, k_{u22})`. -/
def UnitGap {d : ℕ} (L γ η : ℝ) (β : Fin 4 → Mom d) : Prop :=
  β 0 ≠ β 1 ∧ ‖β 0 - β 1‖ ≤ L ^ (-γ + η)

theorem sumintBoundary_close {d : ℕ} (ζ : ℤˣ) (β ctr : Fin 4 → Mom d) (h : ∀ i, ‖β i - ctr i‖ ≤ 1) (c : Fin 4) :
    ‖sumintBoundary ζ β c - sumintBoundary ζ ctr c‖ ≤ 1 :=
  h _

theorem sumintBoundary_gap_iff {d : ℕ} (ζ : ℤˣ) (L γ η : ℝ) (β : Fin 4 → Mom d) :
    (sumintBoundary ζ β 0 ≠ sumintBoundary ζ β 1 ∧ ‖sumintBoundary ζ β 0 - sumintBoundary ζ β 1‖ ≤ L ^ (-γ + η)) ↔
      UnitGap L γ η β := by
  unfold UnitGap sumintBoundary sumintBoundaryPermutation
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simp only [ite_true, Equiv.swap_apply_left, Equiv.swap_apply_right]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 h.symm, ?_⟩
      rwa [norm_sub_rev]
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => h1 h.symm, ?_⟩
      rwa [norm_sub_rev]
  · have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hn, ite_false, Equiv.refl_apply]

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem hmom_outSet_core (hd : Disj blk) (j : J) {d : ℕ} (L : ℝ) (base : Mom d)
    (z : GNode Gsb.tree → (Fin d → ℤ)) (hz : IsDecoration Gsb z) :
    (∀ c, ∃ nv : Fin d → ℤ,
      sumintBoundary (S.sign (blk j).upper.toNode) (fun i => base + latticePoint L (z (Φ.hmom hd j i))) c =
        base + latticePoint L nv) ∧
    sumintBoundary (S.sign (blk j).upper.toNode) (fun i => base + latticePoint L (z (Φ.hmom hd j i))) 0 -
        sumintBoundary (S.sign (blk j).upper.toNode) (fun i => base + latticePoint L (z (Φ.hmom hd j i))) 1 =
      sumintBoundary (S.sign (blk j).upper.toNode) (fun i => base + latticePoint L (z (Φ.hmom hd j i))) 3 -
        sumintBoundary (S.sign (blk j).upper.toNode) (fun i => base + latticePoint L (z (Φ.hmom hd j i))) 2 := by
  refine ⟨fun c => ⟨z (Φ.hmom hd j (sumintBoundaryPermutation (S.sign (blk j).upper.toNode) c)), rfl⟩, ?_⟩
  apply sumintBoundary_momentum
  have h := Φ.hmom_conservation hd j z hz
  have hsub : ∀ a b : Fin d → ℤ, latticePoint L (a - b) = latticePoint L a - latticePoint L b :=
    fun a b => RegRed.latticePoint_sub L a b
  rcases Int.units_eq_one_or (S.sign (blk j).upper.toNode) with e | e
  · rw [e] at h ⊢
    simp only [Units.val_one, one_smul] at h ⊢
    have := congrArg (latticePoint L) h
    rw [hsub, hsub] at this
    show (base + latticePoint L (z (Φ.hmom hd j 0))) - (base + latticePoint L (z (Φ.hmom hd j 1))) =
      (base + latticePoint L (z (Φ.hmom hd j 2))) - (base + latticePoint L (z (Φ.hmom hd j 3)))
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    exact this
  · rw [e] at h ⊢
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h ⊢
    have h' : z (Φ.hmom hd j 1) - z (Φ.hmom hd j 0) = z (Φ.hmom hd j 2) - z (Φ.hmom hd j 3) := by
      rw [← h]; abel
    have := congrArg (latticePoint L) h'
    rw [hsub, hsub] at this
    show -((base + latticePoint L (z (Φ.hmom hd j 0))) - (base + latticePoint L (z (Φ.hmom hd j 1)))) =
      (base + latticePoint L (z (Φ.hmom hd j 2))) - (base + latticePoint L (z (Φ.hmom hd j 3)))
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, neg_sub]
    exact this

end SpliceShape

end WaveTurbulence.VineB
