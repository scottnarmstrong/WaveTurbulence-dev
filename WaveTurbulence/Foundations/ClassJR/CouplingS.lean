/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.TripleS

/-!
# Fixed functions of two affine forms, and the integrals over special variables

For DH21 Lemmas 5.4–5.5 the fixed functions are products `f(x₀) g(x₁)` of two of
`kerM, Φ, χ_∞(x)/x`, where both forms contain the special variable `εα₁`. This module proves

* `kerM_eq_zero_of_one_lt`: the `χ₀` kernel vanishes for `|x| > 1`, with all its derivatives;
* `enorm_iteratedFDeriv_prod2_le`: the Leibniz rule for `x ↦ f(x₀) g(x₁)` on `Fin 2 → ℝ`;
* `lintegral_affine_pair`: `∫ F(X + εs, Y + εs) ds = ∫ F(u, u + Y - X) du` for `ε = ±1`;
* `lintegral_decay_pair_le`: `∫ (1+|u|)^{θ-1} (1+|u+Z|)^{-1} du ≤ Cθ θ` uniformly in `Z`, for
  `0 ≤ θ < 1` (the integrals of DH23 L966–L969, "bounded for all `0 < p < 1`").
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section KerM

theorem kerM_eventually_zero {x : ℝ} (hx : 1 < |x|) (q : ℝ × ℝ) :
    (fun y => kerM y q) =ᶠ[nhds x] fun _ => 0 := by
  filter_upwards [chi0_eventually_zero hx] with y hy
  simp [kerM, hy]

theorem iteratedDeriv_kerM_eq_zero {x : ℝ} (hx : 1 < |x|) (q : ℝ × ℝ) (c : ℕ) :
    iteratedDeriv c (fun y => kerM y q) x = 0 :=
  iteratedDeriv_eq_zero_of_eventuallyEq_zero (kerM_eventually_zero hx q) c

/-- The bound of the `χ₀` kernel with its compact support in `x`. -/
theorem enorm_iteratedDeriv_kerM_le_ind (c : ℕ) (x : ℝ) (q : ℝ × ℝ) :
    ‖iteratedDeriv c (fun y => kerM y q) x‖ₑ ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x * gM c q := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, one_mul]
    exact enorm_iteratedDeriv_kerM_le c x q
  · have h1 : 1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [iteratedDeriv_kerM_eq_zero h1]
    simp

end KerM

section Prod2

/-- `x ↦ f(x₀) g(x₁)` on `Fin 2 → ℝ`. -/
@[expose] def prod2 (f g : ℝ → ℂ) (x : Fin 2 → ℝ) : ℂ := f (x 0) * g (x 1)

theorem norm_proj_le {n : ℕ} (r : Fin n) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_le_pi_norm x r

theorem contDiff_prod2 {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (prod2 f g) :=
  (hf.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff).mul
    (hg.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff)

/-- **Leibniz rule for products of functions of two forms.** -/
theorem enorm_iteratedFDeriv_prod2_le {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (c : ℕ) (x : Fin 2 → ℝ) :
    ‖iteratedFDeriv ℝ c (prod2 f g) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * ‖iteratedDeriv j f (x 0)‖ₑ *
        ‖iteratedDeriv (c - j) g (x 1)‖ₑ := by
  set P0 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
  set P1 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  have h0 : ContDiff ℝ ∞ (f ∘ P0) := hf.comp P0.contDiff
  have h1 : ContDiff ℝ ∞ (g ∘ P1) := hg.comp P1.contDiff
  have : prod2 f g = fun x => (f ∘ P0) x * (g ∘ P1) x := rfl
  rw [this]
  refine (enorm_iteratedFDeriv_mul_le h0 h1 x c).trans (Finset.sum_le_sum fun j _ => ?_)
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · refine (enorm_iteratedFDeriv_comp_le hf P0 (norm_proj_le 0) x j).trans_eq ?_
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rfl
  · refine (enorm_iteratedFDeriv_comp_le hg P1 (norm_proj_le 1) x (c - j)).trans_eq ?_
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rfl

end Prod2

section Integrals

/-- Substitution in the special variable: `∫ F(X + εs, Y + εs) ds = ∫ F(u, u + (Y - X)) du`. -/
theorem lintegral_affine_pair {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (X Y : ℝ) {F : ℝ → ℝ → ℝ≥0∞} :
    ∫⁻ s, F (X + ε * s) (Y + ε * s) = ∫⁻ u, F u (u + (Y - X)) := by
  have key : ∀ s : ℝ, F (X + ε * s) (Y + ε * s) =
      (fun u => F u (u + (Y - X))) (ε * s + X) := fun s => by
    simp only
    congr 1 <;> ring
  simp_rw [key]
  rcases hε with rfl | rfl
  · simp only [one_mul]
    exact lintegral_add_right_eq_self (fun u => F u (u + (Y - X))) X
  · simp only [neg_mul, one_mul]
    rw [lintegral_neg_eq_self (fun s => (fun u => F u (u + (Y - X))) (s + X))]
    exact lintegral_add_right_eq_self (fun u => F u (u + (Y - X))) X

/-- `∫ (1 + |u|)^{-r} du` (finite for `r > 1`). -/
@[expose] noncomputable def Ir (r : ℝ) : ℝ :=
  (∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-r))).toReal

theorem lintegral_Ir_ne_top {r : ℝ} (hr : 1 < r) :
    ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-r)) ≠ ⊤ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  rw [← lt_top_iff_ne_top]
  refine lt_of_le_of_lt (le_of_eq ?_) h.2
  refine lintegral_congr fun u => ?_
  simp only
  rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]

theorem lintegral_Ir_eq {r : ℝ} (hr : 1 < r) :
    ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-r)) = ENNReal.ofReal (Ir r) :=
  (ENNReal.ofReal_toReal (lintegral_Ir_ne_top hr)).symm

/-- The constant of `lintegral_decay_pair_le`. -/
@[expose] noncomputable def Cθ (θ : ℝ) : ℝ :=
  (1 - θ) / 2 * Ir 2 + (1 - (1 - θ) / 2) * Ir (2 / (2 - (1 - θ)))

/-- Weighted AM–GM for the decay product. -/
theorem decay_pair_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (u Z : ℝ) :
    (1 + |u|) ^ (θ - 1) * (1 + |u + Z|) ^ (-1 : ℝ) ≤
      (1 - θ) / 2 * (1 + |u|) ^ (-(2 : ℝ)) +
        (1 - (1 - θ) / 2) * (1 + |u + Z|) ^ (-(2 / (2 - (1 - θ)))) := by
  set p := 1 - θ with hp
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := by linarith
  have ha : 0 < 1 + |u| := by positivity
  have hb : 0 < 1 + |u + Z| := by positivity
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := p / 2) (w₂ := 1 - p / 2)
    (p₁ := (1 + |u|) ^ (-(2 : ℝ))) (p₂ := (1 + |u + Z|) ^ (-(2 / (2 - p))))
    (by positivity) (by linarith) (by positivity) (by positivity) (by ring)
  have e1 : ((1 + |u|) ^ (-(2 : ℝ))) ^ (p / 2) = (1 + |u|) ^ (θ - 1) := by
    rw [← Real.rpow_mul ha.le]
    congr 1
    rw [hp]; ring
  have e2 : ((1 + |u + Z|) ^ (-(2 / (2 - p)))) ^ (1 - p / 2) = (1 + |u + Z|) ^ (-1 : ℝ) := by
    rw [← Real.rpow_mul hb.le]
    congr 1
    have : 2 - p ≠ 0 := by linarith
    field_simp
  rw [e1, e2] at h
  exact h

/-- **The uniform integral of a pair of decaying factors** (DH21 L1014, DH23 L966–L969). -/
theorem lintegral_decay_pair_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (Z : ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (θ - 1) * (1 + |u + Z|) ^ (-1 : ℝ)) ≤
      ENNReal.ofReal (Cθ θ) := by
  have hr : 1 < 2 / (2 - (1 - θ)) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hw1 : 0 ≤ (1 - θ) / 2 := by linarith
  have hw2 : 0 ≤ 1 - (1 - θ) / 2 := by linarith
  calc ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (θ - 1) * (1 + |u + Z|) ^ (-1 : ℝ))
      ≤ ∫⁻ u : ℝ, (ENNReal.ofReal ((1 - θ) / 2) * ENNReal.ofReal ((1 + |u|) ^ (-(2 : ℝ))) +
          ENNReal.ofReal (1 - (1 - θ) / 2) *
            ENNReal.ofReal ((1 + |u + Z|) ^ (-(2 / (2 - (1 - θ)))))) := by
        refine lintegral_mono fun u => ?_
        rw [← ENNReal.ofReal_mul hw1, ← ENNReal.ofReal_mul hw2,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (decay_pair_le h0 h1 u Z)
    _ = ENNReal.ofReal ((1 - θ) / 2) * ENNReal.ofReal (Ir 2) +
          ENNReal.ofReal (1 - (1 - θ) / 2) * ENNReal.ofReal (Ir (2 / (2 - (1 - θ)))) := by
        rw [lintegral_add_left (Measurable.const_mul (by fun_prop) _),
          lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_Ir_eq (by norm_num : (1 : ℝ) < 2)]
        congr 2
        rw [← lintegral_Ir_eq hr]
        exact lintegral_add_right_eq_self
          (fun u => ENNReal.ofReal ((1 + |u|) ^ (-(2 / (2 - (1 - θ)))))) Z
    _ = ENNReal.ofReal (Cθ θ) := by
        have hI2 : 0 ≤ Ir 2 := ENNReal.toReal_nonneg
        have hI3 : 0 ≤ Ir (2 / (2 - (1 - θ))) := ENNReal.toReal_nonneg
        rw [← ENNReal.ofReal_mul hw1, ← ENNReal.ofReal_mul hw2,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rfl

theorem Cθ_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ Cθ θ := by
  unfold Cθ
  have hI2 : 0 ≤ Ir 2 := ENNReal.toReal_nonneg
  have hI3 : 0 ≤ Ir (2 / (2 - (1 - θ))) := ENNReal.toReal_nonneg
  have : 0 ≤ (1 - θ) / 2 := by linarith
  have : 0 ≤ 1 - (1 - θ) / 2 := by linarith
  positivity

end Integrals

end WaveTurbulence.ClassJR
