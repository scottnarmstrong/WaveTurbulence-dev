/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm

/-! # Step 3: V4's recentered kernel is `(δ/2L^{d-γ})^{n₁} ζ · clockedExprEps`

On the `sumint` output set the boundary vector is `sumintBoundary ζ (w̲ + β)` for an integer `β` with the gap relation
(`outSet_exists_beta`), and V4's endpoint `vineChain_eq_sumintForm` together with `clRegionalEpsilon_eq_epsOf` and
`clockedIntegrand_assembly` identifies the kernel with `coupling^{n₁} ζ · clockedExprEps` (`kernel_eq_clockedExprEps`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine VineParamContract
  TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem sumintBoundary_invol {E : Type*} (ζ : ℤˣ) (β : Fin 4 → E) :
    sumintBoundary ζ (sumintBoundary ζ β) = β := by
  funext c
  simp only [sumintBoundary, boundaryPerm_involutive]

/-- A point of the `sumint` output set is `sumintBoundary ζ (w̲ + β)` for an integer `β` with the gap relation. -/
theorem outSet_exists_beta {L : ℝ} (hL : L ≠ 0) (ζ : ℤˣ) (wBar : Mom d) (E : Fin 4 → Mom d)
    (hE : ∀ c, ∃ nv : Fin d → ℤ, E c = wBar + latticePoint L nv) (hgap : E 0 - E 1 = E 3 - E 2) :
    ∃ β : Fin 4 → (Fin d → ℤ), ((ζ : ℤ) • (β 0 - β 1) = β 2 - β 3) ∧
      E = sumintBoundary ζ (fun j => wBar + latticePoint L (β j)) := by
  choose nv hnv using hE
  refine ⟨fun j => nv (sumintBoundaryPermutation ζ j), ?_, ?_⟩
  · have hinj := latticePoint_injective_of_ne_zero (d := d) hL
    apply hinj
    have h : latticePoint L (nv 0) - latticePoint L (nv 1) = latticePoint L (nv 3) - latticePoint L (nv 2) := by
      have := hgap
      rw [hnv 0, hnv 1, hnv 2, hnv 3] at this
      simpa using this
    rcases Int.units_eq_one_or ζ with rfl | rfl
    · simp only [sumintBoundaryPermutation, ite_true, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 1),
        Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 1),
        Units.val_one, one_smul]
      rw [latticePoint_sub, latticePoint_sub, ← neg_sub, h]; abel
    · have hn : (-1 : ℤˣ) ≠ 1 := by decide
      simp only [sumintBoundaryPermutation, hn, ite_false, Equiv.refl_apply, Units.val_neg, Units.val_one,
        neg_one_smul]
      rw [show -(nv 0 - nv 1) = nv 1 - nv 0 by abel, latticePoint_sub, latticePoint_sub, ← neg_sub, h]; abel
  · funext c
    simp only [sumintBoundary, boundaryPerm_involutive]
    exact hnv c

end WaveTurbulence.VineEstS3
