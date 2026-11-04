/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockTraceBudget
public import WaveTurbulence.Foundations.RegAsymp.WickLargeOrder
import Mathlib.Tactic

/-! # Uniform factorial budget for all simultaneous Wick energy traces -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- Summing the cube trace terms costs one factorial per frozen block,
rather than a factorial in the unrestricted ambient dimension. -/
theorem derivativeCoefficientEnvelope_blockTrace_mass_uniform_le
    {r : ℕ} (hr : 0 < r) {κ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C)
    {θ N A : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) :
    (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (blockTraceSymbol C) lam) ≤
      ENNReal.ofReal ((4*max 1 (4*A))^r*(r:ℝ)^r*((2*r).factorial:ℝ))*
        (ENNReal.ofReal N * ∑' k : ℕ,
          ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  let B := max 1 (4*A)
  let R : ℝ≥0∞ := ∑' k : ℕ,
    ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)
  have hsum : (∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
      (ENNReal.ofReal N*∑' k : ℕ,
        ENNReal.ofReal (A^(k+j)*((2*(k+j)).factorial:ℝ)/(4*k).factorial))) ≤
      (r+1 : ℝ≥0∞) * (ENNReal.ofReal ((r:ℝ)^r)*
        (ENNReal.ofReal N*(ENNReal.ofReal (B^r*(2*r).factorial)*R))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^r)*
          (ENNReal.ofReal N*(ENNReal.ofReal (B^r*(2*r).factorial)*R)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        apply mul_le_mul'
        · apply ENNReal.ofReal_le_ofReal
          exact pow_le_pow_right₀ (by exact_mod_cast hr) hjr
        · exact mul_le_mul' le_rfl (tsum_shifted_gevrey_ratio_ennreal_le_of_le hA hjr)
      _ = _ := by simp
  have hcard : (r+1 : ℝ≥0∞) ≤ (2:ℝ≥0∞)^r := by
    exact_mod_cast Nat.succ_le_of_lt r.lt_two_pow_self
  apply (derivativeCoefficientEnvelope_blockTrace_mass_le hC hN hmain).trans
  calc
    _ ≤ (2:ℝ≥0∞)^r * ((r+1 : ℝ≥0∞) *
        (ENNReal.ofReal ((r:ℝ)^r)*
          (ENNReal.ofReal N*(ENNReal.ofReal (B^r*(2*r).factorial)*R)))) :=
      mul_le_mul' le_rfl hsum
    _ ≤ (2:ℝ≥0∞)^r * ((2:ℝ≥0∞)^r *
        (ENNReal.ofReal ((r:ℝ)^r)*
          (ENNReal.ofReal N*(ENNReal.ofReal (B^r*(2*r).factorial)*R)))) :=
      mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = _ := by
      have he : (4*max 1 (4*A))^r*(r:ℝ)^r*((2*r).factorial:ℝ) =
          (4:ℝ)^r*((r:ℝ)^r*(B^r*(2*r).factorial)) := by dsimp only [B]; ring
      rw [he, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      have hfour : ENNReal.ofReal ((4:ℝ)^r) = (2:ℝ≥0∞)^r*(2:ℝ≥0∞)^r := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num only [ENNReal.ofReal_ofNat]
        rw [← mul_pow]
        norm_num
      rw [hfour]
      dsimp only [R]
      simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ B^r)]
      ac_rfl

/-- The complete source trace mass has only a small power loss per frozen
link, uniformly throughout every fixed polylogarithmic order range. -/
theorem exists_blockTrace_mass_threshold {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (orderExponent : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 1 ≤ L ∧
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^orderExponent →
      ∀ r : ℕ, 0 < r → r ≤ n →
      ∀ (κ : Type) [Fintype κ] (C : (Fin r ⊕ κ → ℝ) → ℝ × ℝ → ℂ),
      SymReg C → ∀ θ N : ℝ, 0 ≤ N →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) →
      (∫⁻ lam, wL θ lam*derivativeCoefficientEnvelope (blockTraceSymbol C) lam) ≤
        ENNReal.ofReal (L^(ε*(r:ℝ))) *
          (ENNReal.ofReal N * ∑' k : ℕ,
            ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  obtain ⟨L₀,hL₀⟩ := exists_wick_block_trace_threshold
    (by positivity : 0 ≤ 4*max 1 (4*A)) hε orderExponent
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨hL1,hbound⟩ := hL₀ L hL
  refine ⟨hL1,?_⟩
  intro n hn r hr hrn κ _ C hC θ N hN hmain
  apply (derivativeCoefficientEnvelope_blockTrace_mass_uniform_le hr hC hN hA hmain).trans
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hbound n hn r hrn)) le_rfl

end WaveTurbulence.RegAsymp
