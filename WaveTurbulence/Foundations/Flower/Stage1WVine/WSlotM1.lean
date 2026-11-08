/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotKer
public import WaveTurbulence.Foundations.Stage1.Represents.RepSupM

/-! # STAGE1W-VINE (O3b): moment-carrying superpositions under multipliers, clock freezes and closures

The vine pieces need the outer slot superpositions with the frequency moment `⟨m/2⟩^θ` (main's `CenSupM`/`SupM`,
R58: the routed slot frequencies become the VINEEST modulations).  STAGE1W-O4 proved the frontier-weighted slot targets
in the moment-free form (`CenSup`/`Sup`).  This file gives the moment-carrying versions of the three operations its
proofs use (copied from O4′'s `Mult`/`SlotKer`, sha256 in `COPIED-SHA256SUMS`, with the moment carried along):
* a bounded multiplier of the momentum (frequencies unchanged);
* freezing a clock coordinate (the frozen frequency becomes `0`, which lowers the moment);
* extension of a superposition of a time-continuous kernel to the closure of the box.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

variable {d : ℕ}

/-- A bounded multiplier of the momentum preserves moment-carrying centred superpositions. -/
theorem CenSupM.mulM {θ : ℝ} {r A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSupM θ A B f μ) {c : Mom d → ℂ} {K : ℝ} (hK : 0 < K) (hc : IsMult A c K) :
    CenSupM θ A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, fun l => K * w l, m, n, fun l k => (K⁻¹ : ℂ) * (c k * a l k), fun l => ?_, h2.mul_left K,
    fun l => ?_, fun l k hk => ?_, fun t ht k => ?_, ?_⟩
  · exact mul_nonneg hK.le (h1 l)
  · refine (VineEstS3.Eng.SNorm_smul_le A 0 _ _).trans ?_
    have e : ‖(K⁻¹ : ℂ)‖ₑ = ENNReal.ofReal K⁻¹ := by
      rw [← ofReal_norm, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hK)]
    rw [e]
    calc ENNReal.ofReal K⁻¹ * SNorm A 0 (fun k => c k * a l k) ≤ ENNReal.ofReal K⁻¹ * ENNReal.ofReal K :=
          mul_le_mul_right (hc _ (h3 l)) _
      _ = 1 := by rw [← ENNReal.ofReal_mul (inv_pos.mpr hK).le, inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := (h5 t ht k).mul_left (c k)
    convert hs using 1
    funext l
    have hK' : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    push_cast
    field_simp
  · have e : ∀ l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (K * w l) =
        ENNReal.ofReal K * (maxBracketPow θ (half (m l)) * ENNReal.ofReal (w l)) := fun l => by
      rw [ENNReal.ofReal_mul hK.le]; ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right h6 _

/-- A bounded multiplier of the momentum preserves moment-carrying superpositions. -/
theorem SupM.mulM {θ : ℝ} {r A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : SupM θ A B f μ) {c : Mom d → ℂ} {K : ℝ} (hK : 0 < K) (hc : IsMult A c K) :
    SupM θ A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, fun l => K * w l, m, fun l k => (K⁻¹ : ℂ) * (c k * a l k), fun l => ?_, h2.mul_left K,
    fun l => ?_, fun t ht k => ?_, ?_⟩
  · exact mul_nonneg hK.le (h1 l)
  · refine (VineEstS3.Eng.SNorm_smul_le A 0 _ _).trans ?_
    have e : ‖(K⁻¹ : ℂ)‖ₑ = ENNReal.ofReal K⁻¹ := by
      rw [← ofReal_norm, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hK)]
    rw [e]
    calc ENNReal.ofReal K⁻¹ * SNorm A 0 (fun k => c k * a l k) ≤ ENNReal.ofReal K⁻¹ * ENNReal.ofReal K :=
          mul_le_mul_right (hc _ (h3 l)) _
      _ = 1 := by rw [← ENNReal.ofReal_mul (inv_pos.mpr hK).le, inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  · have hs := (h5 t ht k).mul_left (c k)
    convert hs using 1
    funext l
    have hK' : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    push_cast
    field_simp
  · have e : ∀ l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (K * w l) =
        ENNReal.ofReal K * (maxBracketPow θ (half (m l)) * ENNReal.ofReal (w l)) := fun l => by
      rw [ENNReal.ofReal_mul hK.le]; ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right h6 _

/-- Zeroing one frequency coordinate lowers the moment weight. -/
theorem maxBracketPow_update_le {θ : ℝ} (hθ : 0 ≤ θ) (m : Fin 2 → ℤ) (i : Fin 2) :
    maxBracketPow θ (half (Function.update m i 0)) ≤ maxBracketPow θ (half m) := by
  unfold maxBracketPow
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (zero_le_one.trans le_sup_right) ?_ hθ)
  refine sup_le_sup_right (Real.iSup_le (fun j => ?_) (Real.iSup_nonneg fun _ => Real.sqrt_nonneg _)) 1
  by_cases hj : j = i
  · subst hj
    have : half (Function.update m j 0) j = 0 := by simp [half]
    rw [this]
    refine le_trans (by simp [sq_nonneg]) (le_ciSup (f := fun j : Fin 2 => Real.sqrt (1 + half m j ^ 2))
      (Set.finite_range _).bddAbove j)
  · have : half (Function.update m i 0) j = half m j := by simp [half, Function.update_of_ne hj]
    rw [this]
    exact le_ciSup (f := fun j : Fin 2 => Real.sqrt (1 + half m j ^ 2)) (Set.finite_range _).bddAbove j

/-- **Freezing the first time coordinate** of a moment-carrying centred superposition. -/
theorem CenSupM.update0 {θ : ℝ} (hθ : 0 ≤ θ) {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : CenSupM θ A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 0 c ∈ B) :
    CenSupM θ A B' (fun t k => f (Function.update t 0 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 0 0, n,
    fun l k => (Real.fourierChar (c * ((m l 0 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_, fun l k hk => ?_,
    fun t ht k => ?_, ?_⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update0]
    ring
  · exact le_trans (ENNReal.tsum_le_tsum fun l => mul_le_mul' (maxBracketPow_update_le hθ (m l) 0) le_rfl) h6

/-- **Freezing the second time coordinate** of a moment-carrying centred superposition. -/
theorem CenSupM.update1 {θ : ℝ} (hθ : 0 ≤ θ) {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : CenSupM θ A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 1 c ∈ B) :
    CenSupM θ A B' (fun t k => f (Function.update t 1 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 1 0, n,
    fun l k => (Real.fourierChar (c * ((m l 1 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_, fun l k hk => ?_,
    fun t ht k => ?_, ?_⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · refine h4 l k ?_
    intro h0
    apply hk
    simp [h0]
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update1]
    ring
  · exact le_trans (ENNReal.tsum_le_tsum fun l => mul_le_mul' (maxBracketPow_update_le hθ (m l) 1) le_rfl) h6

/-- **Freezing the first time coordinate** of a moment-carrying superposition. -/
theorem SupM.update0 {θ : ℝ} (hθ : 0 ≤ θ) {A : ℕ} {B B' : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : SupM θ A B f μ) (c : ℝ) (hB : ∀ t ∈ B', Function.update t 0 c ∈ B) :
    SupM θ A B' (fun t k => f (Function.update t 0 c) k) μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, fun l => Function.update (m l) 0 0,
    fun l k => (Real.fourierChar (c * ((m l 0 : ℝ) / 2)) : ℂ) * a l k, h1, h2, fun l => ?_,
    fun t ht k => ?_, ?_⟩
  · exact (snorm_unit_mul_le _ (Circle.norm_coe _) _).trans (h3 l)
  · have hs := h5 _ (hB t ht) k
    convert hs using 1
    funext l
    rw [fsPhase_update0]
    ring
  · exact le_trans (ENNReal.tsum_le_tsum fun l => mul_le_mul' (maxBracketPow_update_le hθ (m l) 0) le_rfl) h6

/-- Agreement on the box transports a moment-carrying centred superposition. -/
theorem CenSupM.congr' {θ : ℝ} {r A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSupM θ A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : CenSupM θ A B g μ := by
  obtain ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Λ, hcnt, w, m, n, a, h1, h2, h3, h4, fun t ht k => (hfg t ht k) ▸ h5 t ht k, h6⟩

/-- Agreement on the box transports a moment-carrying superposition. -/
theorem SupM.congr' {θ : ℝ} {r A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : SupM θ A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : SupM θ A B g μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  exact ⟨Λ, hcnt, w, m, a, h1, h2, h3, fun t ht k => (hfg t ht k) ▸ h5 t ht k, h6⟩

/-- **A moment-carrying superposition of a time-continuous kernel extends to the closure of the box.** -/
theorem SupM.closure_of_continuous {θ : ℝ} {r A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : SupM θ A B f μ) (hf : ∀ k, Continuous fun t => f t k) : SupM θ A (closure B) f μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, m, a, h1, h2, h3, fun t ht k => ?_, h6⟩
  have hb : ∀ l t', ‖(w l : ℂ) * a l k * fsPhase (m l) t'‖ ≤ w l := by
    intro l t'
    rw [norm_mul, norm_mul, norm_fsPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h1 l)]
    exact mul_le_of_le_one_right (h1 l) (snorm_le_one_pointwise _ _ (h3 l) k)
  have hsum : ∀ t', Summable (fun l => (w l : ℂ) * a l k * fsPhase (m l) t') :=
    fun t' => Summable.of_norm_bounded h2 (hb · t')
  have hcont : Continuous (fun t' => ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t') :=
    continuous_tsum (fun l => continuous_const.mul (continuous_fsPhase (m l))) h2 (fun l t' => hb l t')
  have hclosed : IsClosed {t' | ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t' = f t' k} :=
    isClosed_eq hcont (hf k)
  have hBsub : B ⊆ {t' | ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t' = f t' k} :=
    fun t' ht' => (h5 t' ht' k).tsum_eq
  have heq := hclosed.closure_subset_iff.mpr hBsub ht
  rw [← heq]
  exact (hsum t).hasSum

end WaveTurbulence.Flower.Stage1WVine
