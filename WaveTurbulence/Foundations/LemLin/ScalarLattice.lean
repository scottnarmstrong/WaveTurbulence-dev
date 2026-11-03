/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicWeight
public import WaveTurbulence.Foundations.LemLin.ProductSummation

/-!
# The scalar lattice-summed cubic estimate

TARGET `lemcubic0` in one spatial coordinate. The assumption `|s|,|t|≤L`
gives lattice spacing at least `1/3` after dividing frequencies by the
stationary scale. Both summability and the sum bound are proved.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- The scalar frequency lattice used by Poisson summation. -/
@[expose] def scalarLatticeFrequency (L : ℝ) (ξ : Fin 3 → ℝ) (n : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun i => L * n i + ξ i

/-- TARGET `lemcubic0`, scalar case, with genuine absolute summability. -/
theorem scalarCubic_lattice_sum (f : Fin 3 → ScalarCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (kind : CubicPhase) (s t : ℝ),
      |s| ≤ L → |t| ≤ L → ∀ ξ : Fin 3 → ℝ,
      Summable (fun n : Fin 3 → ℤ =>
        ‖scalarCubicIntegral kind f s t (scalarLatticeFrequency L ξ n)‖) ∧
      (∑' n : Fin 3 → ℤ, ‖scalarCubicIntegral kind f s t (scalarLatticeFrequency L ξ n)‖) ≤
        C / cubicScale s t := by
  obtain ⟨K, hK, hmajor⟩ := scalarCubic_tail_majorant f
  refine ⟨K * scalarTailConstant ^ 3, mul_nonneg hK (pow_nonneg scalarTailConstant_nonneg _), ?_⟩
  intro L hL kind s t hs ht ξ
  let Γ := cubicScale s t
  have hΓ : 0 < Γ := cubicScale_pos s t
  have hΓle : Γ ≤ 3 * L := by dsimp [Γ, cubicScale]; linarith only [hL, hs, ht]
  have hw : 1 / 3 ≤ L / Γ := (le_div_iff₀ hΓ).mpr (by linarith only [hΓle])
  let W : Fin 3 → ℤ → ℝ := fun i n => scalarTailWeight ((L / Γ) * n + ξ i / Γ)
  have hW0 (i : Fin 3) (n : ℤ) : 0 ≤ W i n := scalarTailWeight_nonneg _
  have hW (i : Fin 3) : Summable (W i) := (scalar_lattice_tail hw (ξ i / Γ)).1
  have hWB (i : Fin 3) : (∑' n, W i n) ≤ scalarTailConstant :=
    (scalar_lattice_tail hw (ξ i / Γ)).2
  have hP := summable_pi_product W hW0 hW (fun _ => scalarTailConstant) hWB
  have hPB : (∑' n : Fin 3 → ℤ, ∏ i, W i (n i)) ≤ scalarTailConstant ^ 3 := by
    simpa only [prod_const, card_univ, Fintype.card_fin] using hP.2
  have hbound (n : Fin 3 → ℤ) :
      ‖scalarCubicIntegral kind f s t (scalarLatticeFrequency L ξ n)‖ ≤
        (K / Γ) * ∏ i, W i (n i) := by
    have h := hmajor kind s t (scalarLatticeFrequency L ξ n)
    convert h using 2
    apply prod_congr rfl
    intro i _
    dsimp only [scalarLatticeFrequency, W, Γ]
    congr 1
    ring
  have hcoeff : 0 ≤ K / Γ := div_nonneg hK hΓ.le
  have hS : Summable (fun n : Fin 3 → ℤ =>
      ‖scalarCubicIntegral kind f s t (scalarLatticeFrequency L ξ n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hP.1.mul_left (K / Γ))
  refine ⟨hS, ?_⟩
  calc
    _ ≤ ∑' n : Fin 3 → ℤ, (K / Γ) * ∏ i, W i (n i) :=
      hS.tsum_le_tsum hbound (hP.1.mul_left (K / Γ))
    _ = (K / Γ) * ∑' n : Fin 3 → ℤ, ∏ i, W i (n i) := tsum_mul_left
    _ ≤ (K / Γ) * scalarTailConstant ^ 3 := mul_le_mul_of_nonneg_left hPB hcoeff
    _ = _ := by ring

end WaveTurbulence.LemLin
