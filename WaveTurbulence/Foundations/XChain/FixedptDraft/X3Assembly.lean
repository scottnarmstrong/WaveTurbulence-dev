/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Numerics
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Gates

/-!
# X3: assembly of B1.3 `fixedpoint` (T L780–L794, proof L2306–L2338)

`fixedpoint_of_parts : WTPrefix CplMomBody → WTPrefix Part2Body → Gates.FixedpointGate`.

The ingredients:
- `CplMomBody`: the couple moments of Part 1, from the gates and O-X3-CPL (`cplMoments_of_gates`).
- `Part2Body`: (fixedest3) in event form. The excluded data set is measurable and phase-stable, has
  probability `≤ e^{-4N}/2` on `Fev p`, and outside it `‖𝒴‖, ‖𝒲‖ ≤ 1/2` and `‖𝒳‖ ≤ e^{2N}` on `Z`.
  **This is the temporary obligation O-X3-PART2**, to be proved in `X3-Part2`.

The proof, for each sample and `L ≥ gFix(d, 𝔇)`:
1. Exclude the data outside `SumData ∩ Good1Q ∩ C₂`, by `exists_symmetric_subevent`. The non-rapid data
   are null. Part 1 costs `≤ e^{-4N}/2` (`part1_prob`, `part1Bound_le`) and Part 2 costs `≤ e^{-4N}/2`.
2. On the remaining event, clauses (1)–(2) are `Good1`. Clauses (3)–(6) are `fixedpoint_core` with
   `α = κ = e^{3N}`, `ε₀ = e^{-20N}`, `ρ = e^{-10N}` and `M = e^{2N}`, since `triK ≤ e^{4N}/18`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI
open scoped ENNReal

universe u

/-- **The body of O-X3-PART2** (temporary): (fixedest3), T L2316–L2336, as a phase-stable measurable
condition on `a(p)`. -/
def Part2Body (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∃ C : Set ((Fin P.d → ℤ) → ℂ), MeasurableSet C ∧
    (∀ φ, IsCubicPhase φ → ∀ b ∈ C, (Summable fun k => ‖b k‖) → (fun k => φ k * b k) ∈ C) ∧
    μ (Fev p ∩ {ω | a ω p ∉ C}) ≤ ENNReal.ofReal (Real.exp (-(4 * P.N (p + 1) : ℝ)) / 2) ∧
    ∀ b ∈ C, (Summable fun k => ‖b k‖) →
      ∀ c ∈ ZSpace (d := P.d) P.L (5 / 4 * P.Lambda (p + 1)) p,
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Yop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            2⁻¹ * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c ∧
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Wop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            2⁻¹ * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c ∧
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Xop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            ENNReal.ofReal (Real.exp (2 * P.N (p + 1))) * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c

theorem CplMomBody_update (P : WTParams) (C₁ C₂ : ℝ) :
    CplMomBody.{u} {P with C₁ := C₁, C₂ := C₂} = CplMomBody.{u} P := by
  simp only [CplMomBody, AnsatzAt, truncSum, inputsF_update_x2, WTParams.theta, WTParams.Lambda,
    N_update_x2, R_update_x2, cplRand, cplBound]

/-- The threshold for `L`. -/
noncomputable def gFix (d D : ℕ) : ℝ :=
  max (Real.exp (100 * d + 11)) (max (16 * 2 ^ (d + 1) * latConst d)
    (18 * 3 ^ (5 / 4 * ((40 * d) ^ D : ℕ) + 1 : ℝ) * 4 ^ (d + 1) * latConst d ^ 2))

/-! ## Scalar facts -/

theorem fix_small {N K : ℝ} (hN : 1 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (4 * N) / 18) :
    Real.exp (3 * N) * (Real.exp (-(20 * N)) + 3 * K * Real.exp (-(10 * N)) ^ 2 * Real.exp (3 * N) +
      K * Real.exp (-(10 * N)) ^ 3) ≤ Real.exp (-(10 * N)) := by
  have e1 : Real.exp (3 * N) * Real.exp (-(20 * N)) = Real.exp (-(10 * N)) * Real.exp (-(7 * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (3 * N) * (3 * K * Real.exp (-(10 * N)) ^ 2 * Real.exp (3 * N)) =
      3 * K * Real.exp (-(4 * N)) * Real.exp (-(10 * N)) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((2 : ℕ) * -(10 * N)) * Real.exp (3 * N) =
        Real.exp (-(4 * N)) * Real.exp (-(10 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination 3 * K * this
  have e3 : Real.exp (3 * N) * (K * Real.exp (-(10 * N)) ^ 3) =
      K * Real.exp (-(4 * N)) * (Real.exp (-(13 * N)) * Real.exp (-(10 * N))) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((3 : ℕ) * -(10 * N)) =
        Real.exp (-(4 * N)) * (Real.exp (-(13 * N)) * Real.exp (-(10 * N))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination K * this
  have hKe : K * Real.exp (-(4 * N)) ≤ 1 / 18 := by
    have h4 : Real.exp (4 * N) * Real.exp (-(4 * N)) = 1 := by rw [← Real.exp_add]; simp
    calc K * Real.exp (-(4 * N)) ≤ Real.exp (4 * N) / 18 * Real.exp (-(4 * N)) := by gcongr
      _ = 1 / 18 := by rw [div_mul_eq_mul_div, h4]
  have h7 : Real.exp (-(7 * N)) ≤ 1 / 2 := by
    have : Real.exp (-(7 * N)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    refine this.trans ?_
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h13 : Real.exp (-(13 * N)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE := Real.exp_pos (-(10 * N))
  have hKe0 : 0 ≤ K * Real.exp (-(4 * N)) := mul_nonneg hK0 (Real.exp_pos _).le
  rw [mul_add, mul_add, e1, e2, e3]
  nlinarith [mul_le_mul_of_nonneg_right h7 hE.le, mul_le_mul_of_nonneg_right hKe hE.le,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h13 hE.le) hKe0]

theorem fix_contr {N K : ℝ} (hN : 1 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (4 * N) / 18) :
    Real.exp (3 * N) * (6 * K * Real.exp (-(10 * N)) * Real.exp (3 * N) + 3 * K * Real.exp (-(10 * N)) ^ 2) ≤
      2⁻¹ := by
  have e1 : Real.exp (3 * N) * (6 * K * Real.exp (-(10 * N)) * Real.exp (3 * N)) = 6 * K * Real.exp (-(4 * N)) := by
    have : Real.exp (3 * N) * Real.exp (-(10 * N)) * Real.exp (3 * N) = Real.exp (-(4 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination 6 * K * this
  have e2 : Real.exp (3 * N) * (3 * K * Real.exp (-(10 * N)) ^ 2) =
      3 * K * Real.exp (-(4 * N)) * Real.exp (-(13 * N)) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((2 : ℕ) * -(10 * N)) = Real.exp (-(4 * N)) * Real.exp (-(13 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination 3 * K * this
  have hKe : K * Real.exp (-(4 * N)) ≤ 1 / 18 := by
    have h4 : Real.exp (4 * N) * Real.exp (-(4 * N)) = 1 := by rw [← Real.exp_add]; simp
    calc K * Real.exp (-(4 * N)) ≤ Real.exp (4 * N) / 18 * Real.exp (-(4 * N)) := by gcongr
      _ = 1 / 18 := by rw [div_mul_eq_mul_div, h4]
  have h13 : Real.exp (-(13 * N)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hKe0 : 0 ≤ K * Real.exp (-(4 * N)) := mul_nonneg hK0 (Real.exp_pos _).le
  rw [mul_add, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left h13 hKe0]

theorem Lambda_ge (P : WTParams) {p : ℕ} (hp : p < P.D) (hd : 1 ≤ P.d) :
    40 * P.d ≤ P.Lambda (p + 1) ∧ P.Lambda (p + 1) ≤ (40 * P.d) ^ P.D := by
  unfold WTParams.Lambda
  have h1 : 1 ≤ 40 * P.d := by omega
  refine ⟨?_, Nat.pow_le_pow_right h1 (by omega)⟩
  exact Nat.le_self_pow (by omega) _

/-! ## The assembly -/

end WaveTurbulence.Fixedpt
