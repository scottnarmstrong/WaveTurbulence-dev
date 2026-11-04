/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.NormShift
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.WKE.TaylorGateNorm

/-!
# The inputs `F_r = φ(δr) + R_r` are uniformly bounded in `𝔖^{40d,40d}` (TARGET L1173)

TARGET L1173: "the inputs `F_r = φ(δr) + R_r` … are also real valued, and are bounded in the same regularity space".
Here:

* `SNormR_schwartz_le`: a Schwartz function's `𝔖^{Λ₁,Λ₂}` norm is bounded by its Schwartz seminorms;
* `exists_SNormR_bound_of_continuousOn`: a solution `τ ↦ φ(τ)` continuous into the Schwartz space on `[0, τ★]`
  (`IsWKESolution`) is uniformly bounded in `𝔖^{Λ₁,Λ₂}` there;
* `SNormR_add_le`: the triangle inequality for `𝔖^{Λ₁,Λ₂}` (for `C^{Λ₁}` functions);
* **`SNormR_input_le`**: `‖φ(τ) + R‖_{𝔖^{Λ₁,Λ₂}} ≤ B + ε` from `‖φ(τ)‖ ≤ B` and `‖R‖ ≤ ε` (`Λ₁ ≥ 1`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace WaveTurbulence.Regref

variable {d : ℕ}

/-- `‖f‖_{𝔖^{Λ₁,Λ₂}} ≤ 2^{Λ₂} max_{(k,n) ≤ (Λ₂,Λ₁)} ‖f‖_{k,n}` for a Schwartz function. -/
theorem SNormR_schwartz_le (f : 𝓢(Mom d, ℝ)) (Λ₁ Λ₂ : ℕ) :
    SNormR Λ₁ Λ₂ f ≤ ENNReal.ofReal (2 ^ Λ₂ *
      (Finset.Iic (Λ₂, Λ₁)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) := by
  rw [NormBridgeScratch.SNormR_eq_spatialNorm]
  refine WKE.spatialNorm_real_le_of_weighted_derivatives f (by positivity) fun r hr k => ?_
  rw [Real.rpow_natCast]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (m := (Λ₂, Λ₁)) le_rfl hr f k

/-- **A solution continuous into the Schwartz space is uniformly bounded in `𝔖^{Λ₁,Λ₂}` on a compact interval.** -/
theorem exists_SNormR_bound_of_continuousOn {φ : ℝ → 𝓢(Mom d, ℝ)} {T : ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) (Λ₁ Λ₂ : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Icc 0 T, SNormR Λ₁ Λ₂ (φ τ) ≤ ENNReal.ofReal B := by
  set s := Finset.Iic (Λ₂, Λ₁) with hs
  have hb : ∀ m ∈ s, ∃ b : ℝ, ∀ τ ∈ Icc 0 T, SchwartzMap.seminorm ℝ m.1 m.2 (φ τ) ≤ b := by
    intro m _
    have hc : Continuous (SchwartzMap.seminorm ℝ m.1 m.2 : 𝓢(Mom d, ℝ) → ℝ) :=
      (schwartz_withSeminorms ℝ (Mom d) ℝ).continuous_seminorm m
    obtain ⟨b, hb⟩ := (isCompact_Icc.image_of_continuousOn (hc.comp_continuousOn hφ)).bddAbove
    exact ⟨b, fun τ hτ => hb ⟨τ, hτ, rfl⟩⟩
  choose b hb using hb
  refine ⟨2 ^ Λ₂ * ∑ m ∈ s.attach, max (b m.1 m.2) 0, by positivity, fun τ hτ => ?_⟩
  refine (SNormR_schwartz_le (φ τ) Λ₁ Λ₂).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => le_max_right _ _) fun m hm => ?_
  · refine le_trans ?_ (Finset.single_le_sum (f := fun m : s => max (b m.1 m.2) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_attach s ⟨m, hm⟩))
    exact (hb m hm τ hτ).trans (le_max_left _ _)

theorem contDiff_ofReal_iff {n : ℕ} (f : Mom d → ℝ) :
    ContDiff ℝ n (fun k => (f k : ℂ)) ↔ ContDiff ℝ n f := by
  constructor
  · intro h
    have := Complex.reCLM.contDiff.comp h
    convert this using 1
    funext k
    simp
  · intro h
    exact Complex.ofRealCLM.contDiff.comp h

/-- A finite `𝔖^{Λ₁,Λ₂}` norm with `Λ₁ ≥ 1` forces `C^{Λ₁}` (the norm is `⊤` otherwise). -/
theorem contDiff_of_SNormR_ne_top {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) {f : Mom d → ℝ} (h : SNormR Λ₁ Λ₂ f ≠ ⊤) :
    ContDiff ℝ Λ₁ f := by
  rw [← contDiff_ofReal_iff]
  by_contra hc
  apply h
  simp only [SNormR, SNorm, hΛ, false_or, hc, ↓reduceIte]

theorem momentumSupNorm_add_le (Λ : ℕ) (f g : Mom d → ℂ) :
    Fourier.momentumSupNorm Λ (f + g) ≤ Fourier.momentumSupNorm Λ f + Fourier.momentumSupNorm Λ g := by
  unfold Fourier.momentumSupNorm
  refine iSup_le fun k => ?_
  refine le_trans ?_ (add_le_add (le_iSup _ k) (le_iSup _ k))
  rw [← mul_add]
  gcongr
  exact enorm_add_le _ _

/-- **The triangle inequality for `𝔖^{Λ₁,Λ₂}`.** -/
theorem SNormR_add_le {Λ₁ Λ₂ : ℕ} {f g : Mom d → ℝ} (hf : ContDiff ℝ Λ₁ f) (hg : ContDiff ℝ Λ₁ g) :
    SNormR Λ₁ Λ₂ (fun k => f k + g k) ≤ SNormR Λ₁ Λ₂ f + SNormR Λ₁ Λ₂ g := by
  rw [NormBridgeScratch.SNormR_eq_spatialNorm, NormBridgeScratch.SNormR_eq_spatialNorm,
    NormBridgeScratch.SNormR_eq_spatialNorm]
  have hf' := (contDiff_ofReal_iff f).2 hf
  have hg' := (contDiff_ofReal_iff g).2 hg
  have hfg : ContDiff ℝ Λ₁ (fun k => ((f k + g k : ℝ) : ℂ)) := by
    simpa using hf'.add hg'
  unfold Fourier.spatialNorm
  simp only [hfg, hf', hg', or_true, ↓reduceIte]
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun ρ => ?_
  have hsplit : Fourier.momentumDerivative ρ (fun k => ((f k + g k : ℝ) : ℂ)) =
      Fourier.momentumDerivative ρ (fun k => (f k : ℂ)) + Fourier.momentumDerivative ρ (fun k => (g k : ℂ)) := by
    funext k
    have hfn : ContDiff ℝ n (fun k => (f k : ℂ)) := hf'.of_le (by exact_mod_cast hn)
    have hgn : ContDiff ℝ n (fun k => (g k : ℂ)) := hg'.of_le (by exact_mod_cast hn)
    simp only [Fourier.momentumDerivative, Pi.add_apply]
    rw [show (fun k => ((f k + g k : ℝ) : ℂ)) = (fun k => (f k : ℂ)) + fun k => (g k : ℂ) by
      funext k; simp, iteratedFDeriv_add_apply hfn.contDiffAt hgn.contDiffAt]
    rfl
  rw [hsplit]
  refine (momentumSupNorm_add_le _ _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le n (le_iSup_of_le hn (le_iSup (fun ρ : Fin n → Fin d =>
      Fourier.momentumSupNorm Λ₂ (Fourier.momentumDerivative ρ fun k => (f k : ℂ))) ρ))
  · exact le_iSup_of_le n (le_iSup_of_le hn (le_iSup (fun ρ : Fin n → Fin d =>
      Fourier.momentumSupNorm Λ₂ (Fourier.momentumDerivative ρ fun k => (g k : ℂ))) ρ))

/-- **The input bound**: `‖φ + R‖_{𝔖^{Λ₁,Λ₂}} ≤ B + ε` (`Λ₁ ≥ 1`). -/
theorem SNormR_input_le {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) (φ : 𝓢(Mom d, ℝ)) {R : Mom d → ℝ} {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hφ : SNormR Λ₁ Λ₂ φ ≤ ENNReal.ofReal B)
    (hR : SNormR Λ₁ Λ₂ R ≤ ENNReal.ofReal ε) :
    SNormR Λ₁ Λ₂ (fun k => φ k + R k) ≤ ENNReal.ofReal (B + ε) := by
  have hRc : ContDiff ℝ Λ₁ R :=
    contDiff_of_SNormR_ne_top hΛ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hR)
  refine (SNormR_add_le (φ.smooth Λ₁) hRc).trans ?_
  rw [ENNReal.ofReal_add hB hε]
  exact add_le_add hφ hR

end WaveTurbulence.Regref
