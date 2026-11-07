/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreAux

/-! # W5 + W6 for one leaf factor: time-Fourier modes times unit-ball centres

For a kernel `f(t, k)` with `‖f‖_{𝔛^{θ,A,Λ}(B × K)} < b` (`Λ > d`, `A ≠ 0`) this is the combination of the
unit-ball decomposition (L1959) and the time Fourier decomposition (L1961):
`f(t,k) = ∑_{(m,n)} w_{m,n} a_{m,n}(k) e^{πi m·t}` with `a_{m,n}` supported in `|k - a n| ≤ 1`,
`‖a_{m,n}‖_{𝔖^{A,0}} ≤ 1` and `∑_{(m,n)} ⟨m/2⟩^θ w_{m,n} ≤ C b`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS MeasureTheory
open scoped ENNReal ContDiff

variable {r d : ℕ}

theorem fourier_centre_superposition (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ₁ : Λ₁ ≠ 0)
    (hΛ₂ : d < Λ₂) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
      (f : (Fin r → ℝ) → Mom d → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k ∈ K, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B K f < b →
      ∃ (w : (Fin r → ℤ) × (Fin d → ℤ) → ℝ) (a : (Fin r → ℤ) × (Fin d → ℤ) → Mom d → ℂ),
        (∀ p, 0 ≤ w p) ∧ (∀ p, SNorm Λ₁ 0 (a p) ≤ 1) ∧
        (∀ p k, a p k ≠ 0 → ‖k - latPt d p.2‖ ≤ 1) ∧
        (∀ t ∈ B, ∀ k ∈ K, HasSum (fun p => (w p : ℂ) * a p k * fsPhase p.1 t) (f t k)) ∧
        Summable w ∧
        ∑' p, maxBracketPow θ (half p.1) * ENNReal.ofReal (w p) ≤ C * b := by
  obtain ⟨C1, hC1, hfs⟩ := fourier_superposition (r := r) (d := d) hθ hΛ₁ (Λ₂ := Λ₂)
  obtain ⟨C2, hC2pos, hcs⟩ := tsum_snorm_chi_mul_le hd Λ₁ hΛ₂
  refine ⟨ENNReal.ofReal C2 * C1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC1,
    fun q B K f b hb hBc hBi hfc hn => ?_⟩
  obtain ⟨w, a, hw0, ha, hser, hwsum, hbound⟩ := hfs q B K f b hb hBc hBi hfc hn
  have hcd : ∀ m, ContDiff ℝ Λ₁ (a m) := fun m =>
    contDiff_of_SNorm_ne_top hΛ₁ (ne_top_of_le_ne_top ENNReal.one_ne_top (ha m))
  -- the pieces and their norms
  have hsum_n : ∀ m, ∑' n, SNorm Λ₁ 0 (fun k => chiC d n k * a m k) ≤ ENNReal.ofReal C2 := fun m =>
    (hcs (a m) (hcd m)).trans (by simpa using mul_le_mul_right (ha m) (ENNReal.ofReal C2))
  have hfin : ∀ m n, SNorm Λ₁ 0 (fun k => chiC d n k * a m k) ≠ ⊤ := fun m n =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((ENNReal.le_tsum (f := fun n => SNorm Λ₁ 0 (fun k => chiC d n k * a m k)) n).trans (hsum_n m))
  choose u A' hu0 hue hA' hPA hnz using fun (p : (Fin r → ℤ) × (Fin d → ℤ)) =>
    exists_normalised (Λ₁ := Λ₁) (Λ₂ := 0) (fun k => chiC d p.2 k * a p.1 k) (hfin p.1 p.2)
  have hmain : ∑' p : (Fin r → ℤ) × (Fin d → ℤ), maxBracketPow θ (half p.1) *
      ENNReal.ofReal (w p.1 * u p) ≤ ENNReal.ofReal C2 * C1 * b := by
    rw [ENNReal.tsum_prod' (f := fun p : (Fin r → ℤ) × (Fin d → ℤ) =>
      maxBracketPow θ (half p.1) * ENNReal.ofReal (w p.1 * u p))]
    calc ∑' m, ∑' n, maxBracketPow θ (half m) * ENNReal.ofReal (w m * u (m, n))
        = ∑' m, (maxBracketPow θ (half m) * ENNReal.ofReal (w m)) *
            ∑' n, SNorm Λ₁ 0 (fun k => chiC d n k * a m k) := by
          refine tsum_congr fun m => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          rw [ENNReal.ofReal_mul (hw0 m), hue (m, n), mul_assoc]
      _ ≤ ∑' m, (maxBracketPow θ (half m) * ENNReal.ofReal (w m)) * ENNReal.ofReal C2 :=
          ENNReal.tsum_le_tsum fun m => mul_le_mul_right (hsum_n m) _
      _ = (∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m)) * ENNReal.ofReal C2 :=
          ENNReal.tsum_mul_right
      _ ≤ (C1 * b) * ENNReal.ofReal C2 := mul_le_mul_left hbound _
      _ = ENNReal.ofReal C2 * C1 * b := by ring
  refine ⟨fun p => w p.1 * u p, A', fun p => mul_nonneg (hw0 p.1) (hu0 p), hA', ?_, ?_, ?_, ?_⟩
  · intro p k hk
    have : chiC d p.2 k * a p.1 k ≠ 0 := hnz p k hk
    exact norm_sub_latPt_le_one_of_chiC_mul_ne_zero this
  · intro t ht k hk
    have h1 := hser t ht k hk
    have hg : HasSum (fun n : Fin d → ℤ => chiC d n k) 1 := by
      have := Complex.hasSum_ofReal.2 (hasSum_chi d k)
      simpa [chiC] using this
    have hphase : ∀ m : Fin r → ℤ, ‖fsPhase m t‖ = 1 := fun m => by
      unfold fsPhase; exact Circle.norm_coe _
    have hbd : ∀ m, ‖(w m : ℂ) * a m k * fsPhase m t‖ ≤ w m := fun m => by
      rw [norm_mul, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_of_nonneg (hw0 m)]
      calc _ ≤ w m * 1 := mul_le_mul_of_nonneg_left (norm_le_one_of_SNorm_le_one (hcd m) (ha m) k) (hw0 m)
        _ = w m := mul_one _
    have hsm : Summable fun x : (Fin r → ℤ) × (Fin d → ℤ) =>
        ‖(w x.1 : ℂ) * a x.1 k * fsPhase x.1 t * chiC d x.2 k‖ := by
      have hsn : Summable fun n : Fin d → ℤ => chi d n k := (hasSum_chi d k).summable
      have := hwsum.mul_of_nonneg hsn hw0 (fun n => chi_nonneg d n k)
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) this
      rw [norm_mul]
      have : ‖chiC d x.2 k‖ = chi d x.2 k := by
        simp [chiC, abs_of_nonneg (chi_nonneg d x.2 k)]
      rw [this]
      exact mul_le_mul_of_nonneg_right (hbd x.1) (chi_nonneg d _ _)
    have h2 := h1.mul hg (Summable.of_norm hsm)
    rw [mul_one] at h2
    refine h2.congr_fun ?_
    intro p
    have hP := hPA p k
    calc ((w p.1 * u p : ℝ) : ℂ) * A' p k * fsPhase p.1 t
        = (w p.1 : ℂ) * ((u p : ℂ) * A' p k) * fsPhase p.1 t := by push_cast; ring
      _ = (w p.1 : ℂ) * (chiC d p.2 k * a p.1 k) * fsPhase p.1 t := by rw [← hP]
      _ = _ := by ring
  · refine summable_of_tsum_ofReal_ne_top (fun p => mul_nonneg (hw0 p.1) (hu0 p)) ?_
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC1) hb)
      ((ENNReal.tsum_le_tsum fun p => le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ _)).trans
        hmain)
  · exact hmain

end WaveTurbulence.RepAnalytic
