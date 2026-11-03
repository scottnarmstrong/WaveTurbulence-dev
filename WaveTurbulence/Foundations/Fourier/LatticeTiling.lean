/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Tactic

/-!
# Integration over integer translates of the unit cube

The tiling identity underlying Poisson summation in arbitrary dimension.
The half-open cube has one representative of every integer orbit.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Fourier

/-- Integer coordinates identify the standard integral lattice with `ℤ^d`. -/
@[expose] noncomputable def integerLatticeEquiv (d : ℕ) : (Fin d → ℤ) ≃
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) :=
  ((Pi.basisFun ℝ (Fin d)).restrictScalars ℤ).equivFun.toEquiv.symm

@[simp] theorem integerLatticeEquiv_coe (d : ℕ) (n : Fin d → ℤ) :
    (integerLatticeEquiv d n : Fin d → ℝ) = fun i => (n i : ℝ) := by
  classical
  ext i
  simp [integerLatticeEquiv, Module.Basis.equivFun_symm_apply,
    Finset.sum_apply, Pi.single_apply]

/-- Decomposition of an integrable function into integrals over the translates
of `[0,1)^d`, used for TARGET's Poisson summations (L1035, L1541, L1575). -/
theorem integral_eq_tsum_unitCube {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (Fin d → ℝ) → E) (hf : Integrable f) :
    (∫ x, f x) = ∑' n : Fin d → ℤ,
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
        f (x + fun i => (n i : ℝ)) := by
  let : VAddInvariantMeasure
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))) (Fin d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup (Fin d → ℝ) volume)
  have h := (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin d)) volume).integral_eq_tsum'' f hf
  rw [ZSpan.fundamentalDomain_pi_basisFun] at h
  rw [h, ← (integerLatticeEquiv d).tsum_eq]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change f ((integerLatticeEquiv d n : Fin d → ℝ) + x) = _
    rw [integerLatticeEquiv_coe, add_comm]

/-- The same tiling identity over the closed cube; boundaries have zero measure. -/
theorem integral_eq_tsum_unitBox {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (Fin d → ℝ) → E) (hf : Integrable f) :
    (∫ x, f x) = ∑' n : Fin d → ℤ,
      ∫ x in Set.Icc (0 : Fin d → ℝ) 1, f (x + fun i => (n i : ℝ)) := by
  rw [integral_eq_tsum_unitCube f hf]
  apply tsum_congr
  intro n
  exact setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc

end WaveTurbulence.Fourier
