/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2APre

/-! # D3-HELPER (P7), shape (a+): a countable sum of weighted interval integrals of one kernel

`tc2a_sum_ivl`: for a kernel `G(y, u)` with `rn_{timeBox p q}(G) ≤ b_G`, weights `|ψ_i| ≤ M_i` and coefficients
`|a_i| ≤ A`, the function `y ↦ Σ'_i a_i ∫_q^{q+1} ψ_i(u) G(y, u) du` on the window `[p, p+1]` has restricted norm
`≤ C · A · b_G · Σ'_i M_i` (`tc_ivl_restr` per term, main's countable Minkowski `XNorm00Restr_tsum_le`, pointwise
summability from `enorm_le_rn`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

/-- A function of two times read with its clocks swapped. -/
theorem tc2a_swap_box (θ q₀ q₁ : ℝ) (f : (Fin 2 → ℝ) → ℂ) :
    rn θ (timeBox q₁ q₀) (fun t => f ![t 1, t 0]) = rn θ (timeBox q₀ q₁) f := by
  have hsw := rn_swap θ (timeBox q₁ q₀) f
  have hpre : ConjCoh.permT swap2 ⁻¹' timeBox q₁ q₀ = timeBox q₀ q₁ := by
    ext x
    simp only [Set.mem_preimage, permT_swap2_apply, timeBox, Set.mem_setOf_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto
  rw [hpre] at hsw
  rw [← hsw]
  exact rn_congr θ fun x _ => by simp only [permT_swap2_apply]

/-- **A countable sum of weighted interval integrals of one kernel.** -/
theorem tc2a_sum_ivl {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {ι : Type} [Countable ι] (p q : ℕ) (a : ι → ℂ) (ψ : ι → ℝ → ℂ) (Me : ι → ℝ)
      (A : ℝ≥0∞) (G : (Fin 2 → ℝ) → ℂ) (bG : ℝ≥0∞), (∀ i, Measurable (ψ i)) → (∀ i u, ‖ψ i u‖ ≤ Me i) →
      (∀ i, ‖a i‖ₑ ≤ A) → Continuous G → rn θ (timeBox (p : ℝ) q) G ≤ bG → bG < ⊤ → A < ⊤ →
      (∑' i, ENNReal.ofReal (Me i)) < ⊤ →
      rn θ (win (p : ℝ)) (fun y => ∑' i, a i * ∫ u in (q : ℝ)..(q + 1), ψ i u * G ![y 0, u]) ≤
        C * (A * bG * ∑' i, ENNReal.ofReal (Me i)) := by
  obtain ⟨Cv, hCv, hivl⟩ := tc_ivl_restr hθ0
  set Cm : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|) * cutNormR |θ| 1 + 1 with hCm
  have hCmf : Cm < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cutNormR_lt_top _ _),
    ENNReal.one_lt_top⟩
  refine ⟨Cm * ENNReal.ofReal Cv, ENNReal.mul_lt_top hCmf ENNReal.ofReal_lt_top, ?_⟩
  intro ι _ p q a ψ Me A G bG hψm hψb hab hGc hGb hbGf hAf hMf
  have hMe0 : ∀ i, 0 ≤ Me i := fun i => (norm_nonneg _).trans (hψb i 0)
  have hBcl : ∀ t ∈ timeBox (p : ℝ) q, t ∈ closure (interior (timeBox (p : ℝ) q)) := fun t ht =>
    VineEstS3.timeBox_subset_closure_interior _ _ ht
  have hsub : ∀ y0 ∈ Icc (p : ℝ) (p + 1), ∀ u ∈ Ioo (q : ℝ) (q + 1), ![y0, u] ∈ timeBox (p : ℝ) q := by
    intro y0 hy0 u hu
    refine ⟨?_, ?_⟩
    · simpa using hy0
    · simpa using (⟨hu.1.le, hu.2.le⟩ : u ∈ Icc (q : ℝ) (q + 1))
  have hGpt : ∀ y0 ∈ Icc (p : ℝ) (p + 1), ∀ u ∈ Ioo (q : ℝ) (q + 1), ‖G ![y0, u]‖ₑ ≤ bG :=
    fun y0 hy0 u hu => (enorm_le_rn hθ0 hBcl hGc (hsub y0 hy0 u hu)).trans hGb
  set tm : ι → (Fin 1 → ℝ) → ℂ := fun i y => a i * ∫ u in (q : ℝ)..(q + 1), ψ i u * G ![y 0, u] with htm
  have htmb : ∀ i, rn θ (win (p : ℝ)) (tm i) ≤ A * (ENNReal.ofReal Cv * ENNReal.ofReal (Me i) * bG) := fun i => by
    refine (tc_rn_mul_le θ _ (a i) _).trans (mul_le_mul' (hab i) ?_)
    exact (hivl (ψ i) (Me i) (hψm i) (hψb i) p q _ hBcl hsub G hGc).trans (mul_le_mul' le_rfl hGb)
  have hsum : ∀ y ∈ win (p : ℝ), Summable fun i => tm i y := by
    intro y hy
    have hb : ∀ i, ‖tm i y‖ₑ ≤ A * (ENNReal.ofReal (Me i) * bG) := by
      intro i
      simp only [htm]
      rw [enorm_mul, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      refine mul_le_mul' (hab i) ((enorm_integral_le_lintegral_enorm _).trans ?_)
      refine (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (Me i) * bG) measurableSet_Ioo
        fun u hu => ?_).trans (le_of_eq ?_)
      · rw [enorm_mul]
        refine mul_le_mul' ?_ (hGpt (y 0) hy u hu)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hψb i u)
      · rw [setLIntegral_const, Real.volume_Ioo, show (q : ℝ) + 1 - q = 1 by ring, ENNReal.ofReal_one, mul_one]
    have hfin : ∑' i, ‖tm i y‖ₑ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      have hre : ∀ i, A * (ENNReal.ofReal (Me i) * bG) = (A * bG) * ENNReal.ofReal (Me i) := fun i => by ring
      simp_rw [hre]
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hAf.ne hbGf.ne) hMf.ne
    refine Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
    simpa only [enorm_eq_nnnorm] using hfin
  have hBc : win (p : ℝ) ⊆ VineEstS3.FS.cell (fun _ : Fin 1 => (p : ℝ)) := fun y hy i => by
    rw [Subsingleton.elim i 0]; exact hy
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hMk := VineEstS3.Mink.XNorm00Restr_tsum_le (ι := ι) hθ0 (fun _ : Fin 1 => (p : ℝ)) hBc
    Set.countable_univ (fun i t (_ : Unit) => tm i t) (fun t _ => ∑' i, tm i t) (fun t ht _ _ => (hsum t ht).hasSum)
  rw [tc2a_cmc_eq] at hMk
  refine (show rn θ (win (p : ℝ)) (fun y => ∑' i, tm i y) ≤ Cm * ∑' i, rn θ (win (p : ℝ)) (tm i) from hMk).trans ?_
  calc Cm * ∑' i, rn θ (win (p : ℝ)) (tm i)
      ≤ Cm * ∑' i, A * (ENNReal.ofReal Cv * ENNReal.ofReal (Me i) * bG) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum htmb)
    _ = Cm * ENNReal.ofReal Cv * (A * bG * ∑' i, ENNReal.ofReal (Me i)) := by
        have hre : ∀ i, A * (ENNReal.ofReal Cv * ENNReal.ofReal (Me i) * bG) =
            (ENNReal.ofReal Cv * (A * bG)) * ENNReal.ofReal (Me i) := fun i => by ring
        simp_rw [hre]
        rw [ENNReal.tsum_mul_left]
        ring

end WaveTurbulence.Flower.ProtPin
