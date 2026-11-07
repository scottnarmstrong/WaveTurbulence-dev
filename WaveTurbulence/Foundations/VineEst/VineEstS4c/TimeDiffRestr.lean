/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiff
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Regref.Trace00
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (c): the time-difference extraction over `XNorm00Restr`

`timeDiff_extraction`: for `0 < η < 1/4`, `0 ≤ θ ≤ η` and a radius `R` there is a finite constant `C`
such that for every `F` (countable output carrier `V`), the divided difference
`(F(τ₀,τ₂) - F(τ₁,τ₂)) / |τ₀-τ₁|^{1-3η}` satisfies
`‖·‖_{𝔛^{θ,0,0}(B₃, K)} ≤ C ‖F‖_{𝔛^{1-η,0,0}(B₂, K)}` whenever `B₃ ⊆ {‖τ‖ ≤ R}` and both
`(τ₀,τ₂), (τ₁,τ₂)` lie in `B₂` for `τ ∈ B₃`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ENNReal ContDiff
open Classical

namespace WaveTurbulence.VineEstS4c.TimeDiff

open WaveTurbulence.Fourier

theorem mixedFourierNorm00_congr_ae {r : ℕ} {V : Type*} (θ : ℝ) {F G : (Fin r → ℝ) → V → ℂ}
    (h : ∀ v, (fun t => F t v) =ᵐ[volume] (fun t => G t v)) :
    mixedFourierNorm00 θ F = mixedFourierNorm00 θ G := by
  have hiff : (∀ v, Integrable (fun t => F t v)) ↔ ∀ v, Integrable (fun t => G t v) :=
    forall_congr' fun v => integrable_congr (h v)
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · have hG := hiff.mp hF
    rw [mixedFourierNorm00_eq_lintegral hF, mixedFourierNorm00_eq_lintegral hG]
    congr 1
    funext ξ
    unfold mixedFourierEnvelope00
    simp_rw [Regref.timeFourier_congr_ae (h _)]
  · have hG : ¬ ∀ v, Integrable (fun t => G t v) := fun hG => hF (hiff.mpr hG)
    rw [mixedFourierNorm00_of_not_integrable hF, mixedFourierNorm00_of_not_integrable hG]

/-- A smooth compactly supported cutoff equal to one on the ball of radius `R`. -/
theorem exists_cutoff (R : ℝ) :
    ∃ κ : (Fin 3 → ℝ) → ℂ, HasCompactSupport κ ∧ ContDiff ℝ ∞ κ ∧ ∀ τ : Fin 3 → ℝ, ‖τ‖ ≤ R → κ τ = 1 := by
  let f : ContDiffBump (0 : Fin 3 → ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  refine ⟨fun τ => (f τ : ℂ), ?_, ?_, ?_⟩
  · exact f.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro τ hτ
    have : τ ∈ Metric.closedBall (0 : Fin 3 → ℝ) f.rIn := by
      rw [mem_closedBall_zero_iff]; show ‖τ‖ ≤ |R| + 1
      linarith [le_abs_self R]
    simp [f.one_of_mem_closedBall this]


/-- **F2** (TARGET `vineest` Step 4, clause (c); L1903): the divided time difference of an
`𝔛^{1-η}` function, with the factor `|τ₀-τ₁|^{-(1-3η)}`, is an `𝔛^θ` function (`θ ≤ η`). -/
theorem timeDiff_extraction {V : Type*} [Countable V] {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4)
    (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : (Fin 2 → ℝ) → V → ℂ) (B2 : Set (Fin 2 → ℝ))
      (B3 : Set (Fin 3 → ℝ)) (K : Set V),
      (∀ τ ∈ B3, ‖τ‖ ≤ R) → (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr θ B3 K (fun τ v => ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (F ![τ 0, τ 2] v - F ![τ 1, τ 2] v)) ≤ C * XNorm00Restr (1 - η) B2 K F := by
  obtain ⟨κ, hκc, hκs, hκ1⟩ := exists_cutoff R
  have hN : timeFourierNorm θ κ < ⊤ := timeFourierNorm_lt_top_of_smooth_compact θ hκc hκs
  refine ⟨ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ + 1,
    ENNReal.add_ne_top.mpr ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN).ne, ENNReal.one_ne_top⟩,
    ?_⟩
  intro F B2 B3 K hR hB
  set C : ℝ≥0∞ := ENNReal.ofReal (CtotB (1 - 3 * η) θ) * timeFourierNorm θ κ + 1 with hC
  have hC0 : C ≠ 0 := by rw [hC]; exact (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))
  have hCt : C ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN).ne, ENNReal.one_ne_top⟩
  unfold XNorm00Restr
  rw [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 hCt]
  refine le_iInf fun hG => ?_
  by_cases htop : XNorm00 (1 - η) G = ⊤
  · rw [htop, ENNReal.mul_top hC0]; exact le_top
  have hfin : mixedFourierNorm00 (1 - η) G < ⊤ := by
    rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact lt_top_iff_ne_top.mpr htop
  obtain ⟨H, hHn, hHae⟩ := timeDiff_extraction_ae hη0 hη4 hθ0 hθη hκc hκs G hfin
  let G' : (Fin 3 → ℝ) → V → ℂ := fun τ v =>
    if τ ∈ B3 ∧ v ∈ K then ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
          (F ![τ 0, τ 2] v - F ![τ 1, τ 2] v) else H τ v
  refine iInf_le_of_le G' (iInf_le_of_le (fun τ hτ v hv => by simp [G', hτ, hv]) ?_)
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00,
    NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  have hcongr : mixedFourierNorm00 θ G' = mixedFourierNorm00 θ H := by
    apply mixedFourierNorm00_congr_ae
    intro v
    filter_upwards [hHae] with τ hτ
    by_cases hc : τ ∈ B3 ∧ v ∈ K
    · simp only [G', if_pos hc]
      rw [hτ v, hκ1 τ (hR τ hc.1), hG _ (hB τ hc.1).1 v hc.2, hG _ (hB τ hc.1).2 v hc.2]
      ring
    · simp only [G', if_neg hc]
  rw [hcongr]
  refine hHn.trans ?_
  rw [hC, add_mul, one_mul]
  exact le_self_add

end WaveTurbulence.VineEstS4c.TimeDiff
