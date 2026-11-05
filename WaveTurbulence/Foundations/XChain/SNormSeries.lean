/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MultilinearCoordinateBound
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
/-! Summable source spatial-norm bounds control the smooth sum with its exact weighted norm. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem norm_momentumDerivative_le_of_SNorm {d A B n : ℕ} (f : Mom d → ℂ)
    (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C)
    (hn : n ≤ A) (ρ : Fin n → Fin d) (x : Mom d) :
    ‖Fourier.momentumDerivative ρ f x‖ ≤ C := by
  have hb : 1 ≤ jbr x ^ B := one_le_pow₀ (one_le_jbr x)
  exact (le_mul_of_one_le_left (norm_nonneg _) hb).trans
    (SNorm_momentum_pointwise f hf C hC h hn ρ x)

theorem norm_iteratedFDeriv_le_of_SNorm {d A B n : ℕ} (f : Mom d → ℂ)
    (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C)
    (hn : n ≤ A) (x : Mom d) : ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * C :=
  multilinear_norm_le_coordinate_bound _ C hC
    (fun ρ => norm_momentumDerivative_le_of_SNorm f hf C hC h hn ρ x)

theorem SNorm_tsum_bound {ι : Type*} [Countable ι] {d A B : ℕ}
    (f : ι → Mom d → ℂ) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (hs : Summable C)
    (hf : ∀ i, ContDiff ℝ A (f i)) (h : ∀ i, SNorm A B (f i) ≤ ENNReal.ofReal (C i)) :
    SNorm A B (fun x => ∑' i, f i x) ≤ ENNReal.ofReal (∑' i, C i) := by
  let v : ℕ → ι → ℝ := fun n i => (d : ℝ) ^ n * C i
  have hv (n : ℕ) (_ : (n : ℕ∞) ≤ A) : Summable (v n) := hs.mul_left _
  have hop (n : ℕ) (i : ι) (x : Mom d) (hn : (n : ℕ∞) ≤ A) :
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ v n i :=
    norm_iteratedFDeriv_le_of_SNorm (f i) (hf i) (C i) (hC i) (h i) (by exact_mod_cast hn) x
  have hsum : ContDiff ℝ A (fun x => ∑' i, f i x) := contDiff_tsum hf hv hop
  apply SNorm_le_of_momentum_bounds _ hsum
  intro n hn ρ x
  have hni : (n : ℕ∞) ≤ A := by exact_mod_cast hn
  have hsi : Summable (fun i => iteratedFDeriv ℝ n (f i) x) :=
    Summable.of_norm_bounded (hv n hni) (fun i => hop n i x hni)
  have he : Fourier.momentumDerivative ρ (fun x => ∑' i, f i x) x =
      ∑' i, Fourier.momentumDerivative ρ (f i) x := by
    unfold Fourier.momentumDerivative
    rw [iteratedFDeriv_tsum_apply hf hv hop hni, tsum_apply hsi]
  have hnorm : Summable (fun i => ‖Fourier.momentumDerivative ρ (f i) x‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => norm_momentumDerivative_le_of_SNorm (f i) (hf i) (C i) (hC i) (h i) hn ρ x) hs
  rw [he]
  calc
    _ ≤ jbr x ^ B * ∑' i, ‖Fourier.momentumDerivative ρ (f i) x‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (pow_nonneg (jbr_pos x).le B)
    _ = ∑' i, jbr x ^ B * ‖Fourier.momentumDerivative ρ (f i) x‖ := tsum_mul_left.symm
    _ ≤ _ := (hnorm.mul_left _).tsum_le_tsum
      (fun i => SNorm_momentum_pointwise (f i) (hf i) (C i) (hC i) (h i) hn ρ x) hs

end WaveTurbulence.Induct
