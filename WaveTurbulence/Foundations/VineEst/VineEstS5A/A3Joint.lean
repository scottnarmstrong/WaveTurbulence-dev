/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Scalar
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffRestr

/-! # The joint three-clock time factor of clause (c): Fourier modes (V5 Step 4d-A, item 2)

`jointTime_modes`: for a two-clock time function `J` with `‖J‖_{𝔛^{1-η,0,0}(B₂)} < β`, the divided time difference
`H(τ₀,τ₁,τ₂) = |τ₀ - τ₁|^{-(1-3η)} (J(τ₀,τ₂) - J(τ₁,τ₂))` has, on a box `B₃ ⊆ Q_q`, a Fourier-series expansion
`H(τ) = ∑_{m ∈ ℤ³} ĥ_m e^{πi m·τ}` for a.e. `τ ∈ B₃`, with `∑_m ⟨m/2⟩^θ |ĥ_m| ≤ C β` (`θ ≤ η`, `η < 1/4`).
This is the time part of one three-clock row; the spatial part is a separated factor (see `A3Rows`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.NormBridgeScratch
  MeasureTheory Set
open scoped ENNReal

/-- **The joint time factor.** -/
theorem jointTime_modes {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (J : (Fin 2 → ℝ) → ℂ) (B2 : Set (Fin 2 → ℝ)) (B3 : Set (Fin 3 → ℝ))
      (q : Fin 3 → ℝ) (β : ℝ≥0∞),
      β ≠ ⊤ → B3 ⊆ cell q → B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ R) →
      (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr (V := Unit) (1 - η) B2 Set.univ (fun ts _ => J ts) < β →
      ∃ ĥ : (Fin 3 → ℤ) → ℂ,
        (∀ᵐ τ : Fin 3 → ℝ, τ ∈ B3 → HasSum (fun m : Fin 3 → ℤ => ĥ m * fsPhase m τ)
          (((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![τ 0, τ 2] - J ![τ 1, τ 2]))) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖ĥ m‖ₑ ≤ C * β := by
  obtain ⟨Ctd, hCtd, hTd⟩ := VineEstS4c.TimeDiff.timeDiff_extraction (V := Unit) hη0 hη4 hθ0 hθη R
  obtain ⟨Cfs, hCfs, hFs⟩ := hcoef_sum_le (r := 3) hθ0
  refine ⟨Cfs * (Ctd + 1), ENNReal.mul_ne_top hCfs (ENNReal.add_ne_top.2 ⟨hCtd, ENNReal.one_ne_top⟩),
    fun J B2 B3 q β hβ hcell hint hR hB hJ => ?_⟩
  have hX := hTd (fun ts _ => J ts) B2 B3 Set.univ hR hB
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hJ
  have hlt : XNorm00Restr θ B3 Set.univ (fun τ (v : Unit) => ((|τ 0 - τ 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) *
      (J ![τ 0, τ 2] - J ![τ 1, τ 2])) < (Ctd + 1) * β := by
    refine lt_of_le_of_lt hX ?_
    calc Ctd * XNorm00Restr (1 - η) B2 Set.univ (fun ts (_ : Unit) => J ts) ≤ Ctd * β :=
          mul_le_mul_right hJ.le _
      _ < (Ctd + 1) * β := by
          rw [mul_comm Ctd β, mul_comm (Ctd + 1) β]
          exact (ENNReal.mul_lt_mul_iff_right hβ0.ne' hβ).2 (ENNReal.lt_add_right hCtd one_ne_zero)
  unfold XNorm00Restr at hlt
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hGB, hGn⟩ := iInf_lt_iff.1 hG
  set g : (Fin 3 → ℝ) → ℂ := fun t => G t () with hg
  have hgn : timeFourierNorm θ g < ⊤ := by
    have : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [this]; exact lt_of_lt_of_le hGn le_top
  refine ⟨hcoef q g, ?_, ?_⟩
  · filter_upwards [scalar_fs_hasSum_ae hθ0 q hcell hint hgn] with τ hτ htB
    have := hτ htB
    simp only [hg] at this
    rwa [hGB τ htB () (Set.mem_univ _)] at this
  · refine (hFs q g).trans ?_
    have h1 : timeFourierNorm θ g = XNorm00 θ G := (XNorm00_unit_eq_timeFourierNorm θ g).symm
    rw [h1]
    rw [mul_assoc]; exact mul_le_mul_right hGn.le _

end WaveTurbulence.VineEstS5A
