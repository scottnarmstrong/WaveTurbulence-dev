/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoff
public import WaveTurbulence.Foundations.Incoh.CutoffMass

/-!
# Uniform absolute lattice mass of the analytic cutoff array

This is an absolute-convergence bound only; the temporal decay theorem
continues to use oscillatory cancellation. Centers are arbitrary.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Finite-support Tonelli over a finite product of nonnegative series. -/
theorem tsum_pi_prod_ennreal_of_finite_support {I U : Type*} [Fintype I]
    (f : I → U → ℝ≥0∞) (hf : ∀ i, (Function.support (f i)).Finite) :
    (∑' p : I → U, ∏ i, f i (p i)) = ∏ i, ∑' p, f i p := by
  classical
  let S (i : I) : Finset U := (hf i).toFinset
  have hz (i : I) (p : U) (hp : p ∉ S i) : f i p = 0 := by
    by_contra hn
    exact hp ((hf i).mem_toFinset.mpr hn)
  calc
    _ = ∑ p ∈ Fintype.piFinset S, ∏ i, f i (p i) := by
      apply tsum_eq_sum
      intro p hp
      have hn : ¬∀ i, p i ∈ S i := by simpa only [Fintype.mem_piFinset] using hp
      obtain ⟨i, hi⟩ := not_forall.mp hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i (p i) hi)
    _ = ∏ i, ∑ p ∈ S i, f i p := (Finset.prod_univ_sum S f).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => (tsum_eq_sum (fun p hp => hz i p hp)).symm)

/-- The inserted link-array cutoffs have uniformly finite absolute lattice mass. -/
theorem tsum_enorm_linkArrayCutoff_le {d : ℕ} {I : Type*} [Fintype I]
    {L : ℝ} (hL : 1 ≤ L) (z : I → Fin d → ℤ) :
    (∑' p : I → Fin d → ℤ, ‖linkArrayCutoff z (latticeMomentumArray L p)‖ₑ) ≤
      ENNReal.ofReal ((5 * L) ^ d) ^ Fintype.card I := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let f := fun i : I => fun p : Fin d → ℤ =>
    ENNReal.ofReal (WeylSums.latticeCutoff (latticePoint L p - halfCellCenter (z i)))
  have hf (i : I) : (Function.support (f i)).Finite :=
    (WeylSums.finite_latticeCutoff hLp (halfCellCenter (z i))).subset
      (fun p hp hz => hp (by simp only [f, hz, ENNReal.ofReal_zero]))
  have hmass (i : I) : (∑' p, f i p) ≤ ENNReal.ofReal ((5 * L) ^ d) := by
    have hs : Summable (fun p : Fin d → ℤ =>
        WeylSums.latticeCutoff (latticePoint L p - halfCellCenter (z i))) :=
      summable_of_hasFiniteSupport (WeylSums.finite_latticeCutoff hLp (halfCellCenter (z i)))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => latticeCutoff_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal (tsum_latticeCutoff_le hL _)
  have he (p : I → Fin d → ℤ) : ‖linkArrayCutoff z (latticeMomentumArray L p)‖ₑ = ∏ i, f i (p i) := by
    rw [← ofReal_norm]
    simp only [linkArrayCutoff, latticeMomentumArray, norm_prod, Complex.norm_real]
    simp_rw [Real.norm_of_nonneg (latticeCutoff_nonneg _)]
    exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => latticeCutoff_nonneg _)
  simp_rw [he]
  rw [tsum_pi_prod_ennreal_of_finite_support f hf]
  calc
    _ ≤ ∏ _i : I, ENNReal.ofReal ((5 * L) ^ d) := Finset.prod_le_prod (fun i _ => hmass i)
    _ = _ := by simp

end WaveTurbulence.Incoh
