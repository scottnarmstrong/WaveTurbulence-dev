/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH15

/-!
# S2 REPRESENTS, VINE-D (16): countable sums of representations

`RepIntC.tsum`: if `val i` has a countable superposition by spliced kernels of `π` with weight mass `≤ B i` for every `i`
of a countable index set and `Σ B i < ∞`, then `Σ' val i` has one with mass `≤ Σ' B i` (the spliced kernels are uniformly
bounded under the amplitude bounds, `norm_splicedKernel_le`).  This sums the per-mode representations of INTERFACE v2.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set
open scoped ENNReal

variable {P : WTParams} {R : ℕ} {π : Stage1Piece P R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem RepIntC.tsum (hS : π.Gsb.IsPlain) (hL : 0 < P.L) {ι : Type} [Countable ι] (val : ι → ℂ) (B : ι → ℝ)
    (hBs : Summable B) (h : ∀ i, RepIntC π tt base roots (val i) (B i)) :
    Summable val ∧ RepIntC π tt base roots (∑' i, val i) (∑' i, B i) := by
  choose Ξ hc w ctr edge hinge freq a1 a2 a3 a4 a5 using h
  have : ∀ i, Countable (Ξ i) := hc
  have hK0 : 0 ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) := by positivity
  have hkb : ∀ p : Σ i, Ξ i, ‖splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2) (hinge p.1 p.2)
      (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) := fun p =>
    norm_splicedKernel_le π.Gsb hS _ (a5 p.1 p.2) P.L hL _ _ _ _ _
  generalize ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order‖ *
      ((((⌊2 * P.L⌋₊ + 2) ^ P.d) ^ Fintype.card (SourcePair π.Gsb) : ℕ) : ℝ) = K at hK0 hkb
  have hWs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2‖ := by
    refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun i => a3 i, ?_⟩
    exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs
  have hWKs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2 * splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hWs.mul_right K)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb p) (norm_nonneg _)
  have hsumval : ∑' p : Σ i, Ξ i, w p.1 p.2 * splicedKernel π.Gsb (π.data tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots = ∑' i, val i := by
    rw [hWKs.of_norm.tsum_sigma' (fun i => hWKs.of_norm.sigma_factor i)]
    exact tsum_congr fun i => (a2 i).symm
  have hvs : Summable val := (hWKs.of_norm.sigma).congr fun i => (a2 i).symm
  refine ⟨hvs, Σ i, Ξ i, inferInstance, fun p => w p.1 p.2, fun p => ctr p.1 p.2, fun p => edge p.1 p.2,
    fun p => hinge p.1 p.2, fun p => freq p.1 p.2, hWKs, hsumval.symm, hWs, ?_, fun p => a5 p.1 p.2⟩
  rw [hWs.tsum_sigma' (fun i => a3 i)]
  exact Summable.tsum_le_tsum a4 (Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs)
    hBs

end WaveTurbulence.Represents
