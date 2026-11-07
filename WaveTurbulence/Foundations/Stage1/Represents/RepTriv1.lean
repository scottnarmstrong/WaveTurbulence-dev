/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreSNorm
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import WaveTurbulence.Foundations.Spine.NormAssembly
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: time-independent slot kernels (trivial couples and trees)

A time-independent profile `H` with `‖H‖_{𝔖^{40d,40d}} ≤ B` is a centred superposition (one time mode, centres by
the partition of unity) of total mass `C B`; the constant function `1` is a one-mode superposition of mass `1`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open scoped ENNReal

theorem cenSup_profile {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Bx : Set (Fin 2 → ℝ)) (H : Mom d → ℝ) (B : ℝ), 0 ≤ B →
      SNormR (40 * d) (40 * d) H ≤ ENNReal.ofReal B →
      CenSup (30 * d) Bx (fun _ k => (H k : ℂ)) (ENNReal.ofReal (C * B)) := by
  obtain ⟨C0, hC0, hsum⟩ := tsum_snorm_chi_mul_le hd (30 * d) (Λ := 30 * d) (by omega)
  refine ⟨C0, hC0, fun Bx H B hB hH => ?_⟩
  set Hc : Mom d → ℂ := fun k => (H k : ℂ) with hHc
  have hH' : SNorm (40 * d) (40 * d) Hc ≤ ENNReal.ofReal B := hH
  have hcd : ContDiff ℝ (40 * d) Hc := WaveTurbulence.Induct.contDiff_of_SNorm_bound (A := 40 * d) (B := 40 * d) (by omega) _ _ hH'
  have h30 : SNorm (30 * d) (30 * d) Hc ≤ ENNReal.ofReal B :=
    SNorm_mono_bound (A := 40 * d) (B := 40 * d) (A' := 30 * d) (B' := 30 * d) (by omega) (by omega) Hc hcd B hB hH'
  have hcd30 : ContDiff ℝ (30 * d) Hc := hcd.of_le (by exact_mod_cast Nat.mul_le_mul_right d (by norm_num : 30 ≤ 40))
  have hs := hsum Hc hcd30
  have hfin : ∑' n : Fin d → ℤ, SNorm (30 * d) 0 (fun k => chiC d n k * Hc k) ≤ ENNReal.ofReal (C0 * B) := by
    refine hs.trans ?_
    rw [ENNReal.ofReal_mul hC0.le]
    exact mul_le_mul_right h30 _
  have hne : ∀ n, SNorm (30 * d) 0 (fun k => chiC d n k * Hc k) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin) (ENNReal.le_tsum (f := fun n : Fin d → ℤ => SNorm (30 * d) 0 (fun k => chiC d n k * Hc k)) n)
  choose w a hw0 hwe ha hca hsupp using fun n : Fin d → ℤ =>
    exists_normalised (Λ₁ := 30 * d) (Λ₂ := 0) (fun k => chiC d n k * Hc k) (hne n)
  have hsumw : ∑' n, ENNReal.ofReal (w n) ≤ ENNReal.ofReal (C0 * B) := by
    refine le_trans (le_of_eq (tsum_congr fun n => hwe n)) hfin
  refine ⟨Fin d → ℤ, inferInstance, w, fun _ => 0, fun n => n, a, hw0, ?_, ha, ?_, ?_, hsumw⟩
  · exact summable_of_tsum_ofReal_ne_top hw0 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumw)
  · intro n k hk
    exact norm_sub_latPt_le_one_of_chiC_mul_ne_zero (hsupp n k hk)
  · intro t _ k
    have h1 := hasSum_chiC_mul Hc k
    have h2 : ∀ n : Fin d → ℤ, (w n : ℂ) * a n k * fsPhase ((fun _ => (0 : Fin 2 → ℤ)) n) t =
        chiC d n k * Hc k := by
      intro n
      rw [fsPhase_eq_prod_fin2]
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
        Finset.prod_const_one, mul_one]
      exact (hca n k).symm
    simp_rw [h2]
    exact h1

theorem snorm_const_one_le {d : ℕ} (A : ℕ) : SNorm A 0 (fun _ : Mom d => (1 : ℂ)) ≤ 1 := by
  have h := SNorm_le_of_momentum_bounds (d := d) (A := A) (B := 0) (fun _ : Mom d => (1 : ℂ))
    contDiff_const 1 (by
      intro n hn ρ x
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [Fourier.momentumDerivative_zero]
      · have : Fourier.momentumDerivative ρ (fun _ : Mom d => (1 : ℂ)) x = 0 := by
          unfold Fourier.momentumDerivative
          rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hpos)]
          rfl
        simp [this])
  simpa using h

theorem sup_one {d : ℕ} (A : ℕ) (Bx : Set (Fin 2 → ℝ)) :
    Sup (d := d) A Bx (fun _ _ => (1 : ℂ)) (1 : ℝ≥0∞) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ _ => (1 : ℂ), fun _ => zero_le_one,
    (hasSum_fintype _).summable, fun _ => snorm_const_one_le A, ?_, ?_⟩
  · intro t _ k
    have : fsPhase (0 : Fin 2 → ℤ) t = 1 := by
      rw [fsPhase_eq_prod_fin2]; simp
    simp [this]
  · simp

end WaveTurbulence.Represents
