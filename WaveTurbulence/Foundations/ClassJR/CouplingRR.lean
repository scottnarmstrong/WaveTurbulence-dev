/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompJR

/-!
# DH21 Lemma 5.5: the uniform double integrals over the two special variables

For the composition of two class `R` operators the couplings depend on three forms
`x₀ = X₀ - ε₁α₁ + ε₂α₂`, `x₁ = X₁ + ε₁α₁`, `x₂ = X₂ + ε₂α₂` of the two special variables, and
DH21 (L1036–L1041) uses the bounds, uniform in `(X₀, X₁, X₂)`,
`∫∫ |M(x₀,σ)| |χ_∞(x₁)/x₁| |χ_∞(x₂)/x₂| dα₁ dα₂ ≤ C⟨σ⟩^{-10}` and
`∫∫ |χ_∞(x₀)/x₀| |χ_∞(x₁)/x₁| |χ_∞(x₂)/x₂| dα₁ dα₂ ≤ C` ("elementary calculus"), together with
their versions with the weight `(1+|x_r|)^θ` on one of the three factors (needed for the weight
of the composed operator, DH21 L1041). We prove the weighted version in the form
`∫∫ Σ_r (1+|x_r|)^θ ∏_r (1+|x_r|)^{-1} dα₁ dα₂ ≤ D3 θ` for `0 ≤ θ < 1`
(`lintegral_tri3_le`); the indicator `1_{|x₀| ≤ 1}` of the support of `M` is at most
`2 (1+|x₀|)^{-1}`.

The proof: after the substitution `(α₁, α₂) ↦ (x₁, x₂)` one has `x₀ = C - x₁ + x₂`; the inner
integral is a decay pair `∫ (1+|u|)^{-a}(1+|u+Z|)^{-b} du ≤ 2^{c+1} I(a+b-c) (1+|Z|)^{-c}`
(`lintegral_pair_decay_le`, from weighted AM–GM and `1+|Z| ≤ 2 max(1+|u|, 1+|u+Z|)`), and the
outer integral is again a pair.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Pair

/-- Weighted AM–GM for a pair of decaying factors. -/
theorem pair_gen_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (u Z : ℝ) :
    (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b) ≤
      a / (a + b) * (1 + |u|) ^ (-(a + b)) + b / (a + b) * (1 + |u + Z|) ^ (-(a + b)) := by
  have hP : 0 < 1 + |u| := by positivity
  have hQ : 0 < 1 + |u + Z| := by positivity
  have hne : a + b ≠ 0 := hab.ne'
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := a / (a + b)) (w₂ := b / (a + b))
    (p₁ := (1 + |u|) ^ (-(a + b))) (p₂ := (1 + |u + Z|) ^ (-(a + b)))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by rw [← add_div, div_self hne])
  have e1 : ((1 + |u|) ^ (-(a + b))) ^ (a / (a + b)) = (1 + |u|) ^ (-a) := by
    rw [← Real.rpow_mul hP.le]; congr 1; field_simp
  have e2 : ((1 + |u + Z|) ^ (-(a + b))) ^ (b / (a + b)) = (1 + |u + Z|) ^ (-b) := by
    rw [← Real.rpow_mul hQ.le]; congr 1; field_simp
  rw [e1, e2] at h
  exact h

/-- **The pair integral** `∫ (1+|u|)^{-a} (1+|u+Z|)^{-b} du ≤ I(a+b)` for `a, b ≥ 0`,
`a + b > 1`. -/
theorem lintegral_pair_gen_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 1 < a + b) (Z : ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b)) ≤
      ENNReal.ofReal (Ir (a + b)) := by
  have hab0 : 0 < a + b := by linarith
  have hw1 : 0 ≤ a / (a + b) := by positivity
  have hw2 : 0 ≤ b / (a + b) := by positivity
  have hI : 0 ≤ Ir (a + b) := ENNReal.toReal_nonneg
  calc ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b))
      ≤ ∫⁻ u : ℝ, (ENNReal.ofReal (a / (a + b)) * ENNReal.ofReal ((1 + |u|) ^ (-(a + b))) +
          ENNReal.ofReal (b / (a + b)) * ENNReal.ofReal ((1 + |u + Z|) ^ (-(a + b)))) := by
        refine lintegral_mono fun u => ?_
        rw [← ENNReal.ofReal_mul hw1, ← ENNReal.ofReal_mul hw2,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (pair_gen_le ha hb hab0 u Z)
    _ = ENNReal.ofReal (a / (a + b)) * ENNReal.ofReal (Ir (a + b)) +
          ENNReal.ofReal (b / (a + b)) * ENNReal.ofReal (Ir (a + b)) := by
        rw [lintegral_add_left (Measurable.const_mul (by fun_prop) _),
          lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_Ir_eq hab]
        congr 2
        rw [← lintegral_Ir_eq hab]
        exact lintegral_add_right_eq_self
          (fun u => ENNReal.ofReal ((1 + |u|) ^ (-(a + b)))) Z
    _ = ENNReal.ofReal (Ir (a + b)) := by
        rw [← ENNReal.ofReal_mul hw1, ← ENNReal.ofReal_mul hw2,
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul, ← add_div,
          div_self hab0.ne', one_mul]

/-- `(1+|Z|)^c ≤ 2^c ((1+|u|)^c + (1+|u+Z|)^c)`. -/
theorem one_add_abs_rpow_le {c : ℝ} (hc : 0 ≤ c) (u Z : ℝ) :
    (1 + |Z|) ^ c ≤ 2 ^ c * ((1 + |u|) ^ c + (1 + |u + Z|) ^ c) := by
  have hP : 0 ≤ 1 + |u| := by positivity
  have hQ : 0 ≤ 1 + |u + Z| := by positivity
  have hZ : 1 + |Z| ≤ 2 * max (1 + |u|) (1 + |u + Z|) := by
    have : |Z| ≤ |u| + |u + Z| := by
      calc |Z| = |-u + (u + Z)| := by rw [neg_add_cancel_left]
        _ ≤ |-u| + |u + Z| := abs_add_le _ _
        _ = |u| + |u + Z| := by rw [abs_neg]
    have h1 := le_max_left (1 + |u|) (1 + |u + Z|)
    have h2 := le_max_right (1 + |u|) (1 + |u + Z|)
    linarith
  calc (1 + |Z|) ^ c ≤ (2 * max (1 + |u|) (1 + |u + Z|)) ^ c :=
        Real.rpow_le_rpow (by positivity) hZ hc
    _ = 2 ^ c * (max (1 + |u|) (1 + |u + Z|)) ^ c :=
        Real.mul_rpow (by norm_num) (le_max_of_le_left hP)
    _ ≤ 2 ^ c * ((1 + |u|) ^ c + (1 + |u + Z|) ^ c) := by
        gcongr
        rcases le_total (1 + |u|) (1 + |u + Z|) with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg hP c]
        · rw [max_eq_left h]; linarith [Real.rpow_nonneg hQ c]

/-- Pointwise form of the decay pair. -/
theorem pair_decay_le {a b c : ℝ} (hc : 0 ≤ c) (u Z : ℝ) :
    (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b) ≤
      2 ^ c * (1 + |Z|) ^ (-c) * ((1 + |u|) ^ (-(a - c)) * (1 + |u + Z|) ^ (-b) +
        (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-(b - c))) := by
  have hP : 0 < 1 + |u| := by positivity
  have hQ : 0 < 1 + |u + Z| := by positivity
  have hR : 0 < 1 + |Z| := by positivity
  have hpe := one_add_abs_rpow_le hc u Z
  have e1 : (1 + |u|) ^ (-(a - c)) = (1 + |u|) ^ (-a) * (1 + |u|) ^ c := by
    rw [← Real.rpow_add hP]; congr 1; ring
  have e2 : (1 + |u + Z|) ^ (-(b - c)) = (1 + |u + Z|) ^ (-b) * (1 + |u + Z|) ^ c := by
    rw [← Real.rpow_add hQ]; congr 1; ring
  have eR : (1 + |Z|) ^ (-c) * (1 + |Z|) ^ c = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  rw [e1, e2]
  have hP0 : 0 ≤ (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b) := by positivity
  calc (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b)
      = (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b) * ((1 + |Z|) ^ (-c) * (1 + |Z|) ^ c) := by
        rw [eR, mul_one]
    _ ≤ (1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b) *
          ((1 + |Z|) ^ (-c) * (2 ^ c * ((1 + |u|) ^ c + (1 + |u + Z|) ^ c))) := by gcongr
    _ = _ := by ring

/-- **The decay pair**: for `0 ≤ c ≤ min(a, b)` and `a + b - c > 1`,
`∫ (1+|u|)^{-a} (1+|u+Z|)^{-b} du ≤ 2^{c+1} I(a+b-c) (1+|Z|)^{-c}`. -/
theorem lintegral_pair_decay_le {a b c : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 1 < a + b - c) (Z : ℝ) :
    ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b)) ≤
      ENNReal.ofReal (2 ^ c * 2 * Ir (a + b - c) * (1 + |Z|) ^ (-c)) := by
  have h1 := lintegral_pair_gen_le (a := a - c) (b := b) (by linarith) (by linarith)
    (by linarith) Z
  have h2 := lintegral_pair_gen_le (a := a) (b := b - c) (by linarith) (by linarith)
    (by linarith) Z
  rw [show a - c + b = a + b - c by ring] at h1
  rw [show a + (b - c) = a + b - c by ring] at h2
  have hK : 0 ≤ 2 ^ c * (1 + |Z|) ^ (-c) := by positivity
  have hI : 0 ≤ Ir (a + b - c) := ENNReal.toReal_nonneg
  calc ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-b))
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (2 ^ c * (1 + |Z|) ^ (-c)) *
          (ENNReal.ofReal ((1 + |u|) ^ (-(a - c)) * (1 + |u + Z|) ^ (-b)) +
            ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-(b - c)))) := by
        refine lintegral_mono fun u => ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (pair_decay_le hc u Z)
    _ = ENNReal.ofReal (2 ^ c * (1 + |Z|) ^ (-c)) *
          ((∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-(a - c)) * (1 + |u + Z|) ^ (-b))) +
            ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |u|) ^ (-a) * (1 + |u + Z|) ^ (-(b - c)))) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop)]
    _ ≤ ENNReal.ofReal (2 ^ c * (1 + |Z|) ^ (-c)) *
          (ENNReal.ofReal (Ir (a + b - c)) + ENNReal.ofReal (Ir (a + b - c))) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add hI hI, ← ENNReal.ofReal_mul hK]
        congr 1; ring

end Pair

section Double

/-- **The double integral** of three decaying factors of `x₀ = C - v + u`, `x₁ = v`, `x₂ = u`. -/
theorem lintegral_tri_le {a₀ a₁ a₂ c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hc0 : c ≤ a₀)
    (hc2 : c ≤ a₂) (h02 : 1 < a₂ + a₀ - c) (h1 : 1 < a₁ + c) (C : ℝ) :
    ∫⁻ v : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |C - v + u|) ^ (-a₀) * (1 + |v|) ^ (-a₁) *
      (1 + |u|) ^ (-a₂)) ≤ ENNReal.ofReal (4 * Ir (a₂ + a₀ - c) * Ir (a₁ + c)) := by
  have hI1 : 0 ≤ Ir (a₂ + a₀ - c) := ENNReal.toReal_nonneg
  have hI2 : 0 ≤ Ir (a₁ + c) := ENNReal.toReal_nonneg
  have h2c : (2 : ℝ) ^ c * 2 ≤ 4 := by
    have : (2 : ℝ) ^ c ≤ 2 := by
      calc (2 : ℝ) ^ c ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
        _ = 2 := Real.rpow_one 2
    linarith
  have hin : ∀ v : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |C - v + u|) ^ (-a₀) *
      (1 + |v|) ^ (-a₁) * (1 + |u|) ^ (-a₂)) ≤ ENNReal.ofReal ((1 + |v|) ^ (-a₁)) *
        ENNReal.ofReal (4 * Ir (a₂ + a₀ - c) * (1 + |v + -C|) ^ (-c)) := fun v => by
    have e : ∀ u : ℝ, ENNReal.ofReal ((1 + |C - v + u|) ^ (-a₀) * (1 + |v|) ^ (-a₁) *
        (1 + |u|) ^ (-a₂)) = ENNReal.ofReal ((1 + |v|) ^ (-a₁)) *
          ENNReal.ofReal ((1 + |u|) ^ (-a₂) * (1 + |u + (C - v)|) ^ (-a₀)) := fun u => by
      rw [← ENNReal.ofReal_mul (by positivity), show C - v + u = u + (C - v) by ring]
      congr 1
      ring
    simp_rw [e]
    rw [lintegral_const_mul _ (by fun_prop)]
    gcongr
    refine (lintegral_pair_decay_le hc hc2 hc0 h02 (C - v)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_sub_comm C v, sub_eq_add_neg v C]
    have : 0 ≤ (1 + |v + -C|) ^ (-c) := by positivity
    gcongr
  calc ∫⁻ v : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal ((1 + |C - v + u|) ^ (-a₀) * (1 + |v|) ^ (-a₁) *
        (1 + |u|) ^ (-a₂))
      ≤ ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v|) ^ (-a₁)) *
          ENNReal.ofReal (4 * Ir (a₂ + a₀ - c) * (1 + |v + -C|) ^ (-c)) := lintegral_mono hin
    _ = ENNReal.ofReal (4 * Ir (a₂ + a₀ - c)) *
          ∫⁻ v : ℝ, ENNReal.ofReal ((1 + |v|) ^ (-a₁) * (1 + |v + -C|) ^ (-c)) := by
        rw [← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_congr fun v => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (4 * Ir (a₂ + a₀ - c)) * ENNReal.ofReal (Ir (a₁ + c)) := by
        gcongr
        exact lintegral_pair_gen_le (by linarith) hc h1 (-C)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- `∫ G` over `Fin 2 → ℝ` as an iterated integral. -/
theorem lintegral_fin2 {G : (Fin 2 → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s, G s = ∫⁻ a, ∫⁻ b, G ![a, b] := by
  have hmp := (volume_preserving_finTwoArrow ℝ).symm _
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.finTwoArrow).symm.measurableEmbedding G,
    Measure.volume_eq_prod,
    lintegral_prod (fun p : ℝ × ℝ => G (MeasurableEquiv.finTwoArrow.symm p))
      (hG.comp (MeasurableEquiv.finTwoArrow).symm.measurable).aemeasurable]
  rfl

/-- **The substitution `(α₁, α₂) ↦ (x₁, x₂)`.** -/
theorem lintegral_two_signs {e₁ e₂ : ℝ} (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (X₀ X₁ X₂ : ℝ) {F : ℝ → ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) :
    ∫⁻ s : Fin 2 → ℝ, F (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1) =
      ∫⁻ v, ∫⁻ u, F (X₀ + X₁ - X₂ - v + u) v u := by
  have hm : Measurable fun s : Fin 2 → ℝ =>
      ((X₀ - e₁ * s 0 + e₂ * s 1, (X₁ + e₁ * s 0, X₂ + e₂ * s 1)) : ℝ × ℝ × ℝ) := by
    fun_prop
  rw [lintegral_fin2 (by exact hF.comp hm)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hin : ∀ a : ℝ, ∫⁻ b, F (X₀ - e₁ * a + e₂ * b) (X₁ + e₁ * a) (X₂ + e₂ * b) =
      ∫⁻ u, F (X₀ + X₁ - X₂ - (X₁ + e₁ * a) + u) (X₁ + e₁ * a) u := fun a => by
    rw [← lintegral_affine_one he₂ X₂
      (f := fun u => F (X₀ + X₁ - X₂ - (X₁ + e₁ * a) + u) (X₁ + e₁ * a) u)]
    refine lintegral_congr fun b => ?_
    congr 1
    ring
  simp_rw [hin]
  exact lintegral_affine_one he₁ X₁ (f := fun v => ∫⁻ u, F (X₀ + X₁ - X₂ - v + u) v u)

/-- Iterated integrals of a sum of three terms. -/
theorem lintegral_lintegral_add3 {F₁ F₂ F₃ : ℝ → ℝ → ℝ≥0∞} (h₁ : Measurable (Function.uncurry F₁))
    (h₂ : Measurable (Function.uncurry F₂)) (h₃ : Measurable (Function.uncurry F₃)) :
    ∫⁻ v, ∫⁻ u, (F₁ v u + F₂ v u + F₃ v u) =
      (∫⁻ v, ∫⁻ u, F₁ v u) + (∫⁻ v, ∫⁻ u, F₂ v u) + ∫⁻ v, ∫⁻ u, F₃ v u := by
  have m₁ : Measurable fun v => ∫⁻ u, F₁ v u := h₁.lintegral_prod_right'
  have m₂ : Measurable fun v => ∫⁻ u, F₂ v u := h₂.lintegral_prod_right'
  have m₃ : Measurable fun v => ∫⁻ u, F₃ v u := h₃.lintegral_prod_right'
  calc ∫⁻ v, ∫⁻ u, (F₁ v u + F₂ v u + F₃ v u)
      = ∫⁻ v, ((∫⁻ u, F₁ v u) + (∫⁻ u, F₂ v u) + ∫⁻ u, F₃ v u) := lintegral_congr fun v => by
        have e1 := lintegral_add_left (μ := volume) (f := fun u => F₁ v u + F₂ v u)
          (h₁.of_uncurry_left.add h₂.of_uncurry_left) (fun u => F₃ v u)
        have e2 := lintegral_add_left (μ := volume) (f := fun u => F₁ v u) h₁.of_uncurry_left
          (fun u => F₂ v u)
        exact e1.trans (congrArg (· + ∫⁻ u, F₃ v u) e2)
    _ = _ := by
        have e1 := lintegral_add_left (μ := volume)
          (f := fun v => (∫⁻ u, F₁ v u) + ∫⁻ u, F₂ v u) (m₁.add m₂) (fun v => ∫⁻ u, F₃ v u)
        have e2 := lintegral_add_left (μ := volume) (f := fun v => ∫⁻ u, F₁ v u) m₁
          (fun v => ∫⁻ u, F₂ v u)
        exact e1.trans (congrArg (· + ∫⁻ v, ∫⁻ u, F₃ v u) e2)

/-- The integrand `Σ_r (1+|x_r|)^θ ∏_r (1+|x_r|)^{-1}`, expanded. -/
@[expose] noncomputable def tri3 (θ x0 x1 x2 : ℝ) : ℝ :=
  (1 + |x0|) ^ (-(1 - θ)) * (1 + |x1|) ^ (-1 : ℝ) * (1 + |x2|) ^ (-1 : ℝ) +
    (1 + |x0|) ^ (-1 : ℝ) * (1 + |x1|) ^ (-(1 - θ)) * (1 + |x2|) ^ (-1 : ℝ) +
      (1 + |x0|) ^ (-1 : ℝ) * (1 + |x1|) ^ (-1 : ℝ) * (1 + |x2|) ^ (-(1 - θ))

theorem tri3_nonneg (θ x0 x1 x2 : ℝ) : 0 ≤ tri3 θ x0 x1 x2 := by
  unfold tri3; positivity

/-- The constant of `lintegral_tri3_le`. -/
@[expose] noncomputable def D3 (θ : ℝ) : ℝ := 12 * (Ir ((3 - θ) / 2) * Ir ((3 - θ) / 2))

theorem D3_nonneg (θ : ℝ) : 0 ≤ D3 θ := by
  have : 0 ≤ Ir ((3 - θ) / 2) := ENNReal.toReal_nonneg
  unfold D3; positivity

/-- **The weighted double integral of DH21 Lemma 5.5** (L1036–L1041), uniform in
`(X₀, X₁, X₂)`. -/
theorem lintegral_tri3_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {e₁ e₂ : ℝ}
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) (X₀ X₁ X₂ : ℝ) :
    ∫⁻ s : Fin 2 → ℝ, ENNReal.ofReal
      (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) ≤
        ENNReal.ofReal (D3 θ) := by
  have hF : Measurable fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (tri3 θ p.1 p.2.1 p.2.2) := by
    unfold tri3; fun_prop
  rw [lintegral_two_signs he₁ he₂ X₀ X₁ X₂ (F := fun a b c => ENNReal.ofReal (tri3 θ a b c)) hF]
  set C := X₀ + X₁ - X₂
  set r := (3 - θ) / 2
  have hI : 0 ≤ Ir r := ENNReal.toReal_nonneg
  have t1 := lintegral_tri_le (a₀ := 1 - θ) (a₁ := 1) (a₂ := 1) (c := (1 - θ) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) C
  have t2 := lintegral_tri_le (a₀ := 1) (a₁ := 1 - θ) (a₂ := 1) (c := (1 + θ) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) C
  have t3 := lintegral_tri_le (a₀ := 1) (a₁ := 1) (a₂ := 1 - θ) (c := (1 - θ) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) C
  rw [show (1 : ℝ) + (1 - θ) - (1 - θ) / 2 = r by ring,
    show (1 : ℝ) + (1 - θ) / 2 = r by ring] at t1
  rw [show (1 : ℝ) + 1 - (1 + θ) / 2 = r by ring,
    show (1 : ℝ) - θ + (1 + θ) / 2 = r by ring] at t2
  rw [show (1 : ℝ) - θ + 1 - (1 - θ) / 2 = r by ring,
    show (1 : ℝ) + (1 - θ) / 2 = r by ring] at t3
  have hsplit : ∀ v u : ℝ, ENNReal.ofReal (tri3 θ (C - v + u) v u) =
      ENNReal.ofReal ((1 + |C - v + u|) ^ (-(1 - θ)) * (1 + |v|) ^ (-1 : ℝ) *
        (1 + |u|) ^ (-1 : ℝ)) +
      ENNReal.ofReal ((1 + |C - v + u|) ^ (-1 : ℝ) * (1 + |v|) ^ (-(1 - θ)) *
        (1 + |u|) ^ (-1 : ℝ)) +
      ENNReal.ofReal ((1 + |C - v + u|) ^ (-1 : ℝ) * (1 + |v|) ^ (-1 : ℝ) *
        (1 + |u|) ^ (-(1 - θ))) := fun v u => by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rfl
  simp_rw [hsplit]
  have hm : ∀ a₀ a₁ a₂ : ℝ, Measurable (Function.uncurry fun v u : ℝ => ENNReal.ofReal
      ((1 + |C - v + u|) ^ (-a₀) * (1 + |v|) ^ (-a₁) * (1 + |u|) ^ (-a₂))) :=
    fun a₀ a₁ a₂ => by unfold Function.uncurry; fun_prop
  rw [lintegral_lintegral_add3 (hm _ _ _) (hm _ _ _) (hm _ _ _)]
  refine (add_le_add (add_le_add t1 t2) t3).trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [D3, r]
  ring

end Double

section Prod3

/-- `x ↦ f(x₀) (g(x₁) h(x₂))` on `Fin 3 → ℝ`. -/
@[expose] def prod3 (f g h : ℝ → ℂ) (x : Fin 3 → ℝ) : ℂ := f (x 0) * (g (x 1) * h (x 2))

theorem contDiff_prod3 {f g h : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (prod3 f g h) :=
  (hf.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff).mul
    ((hg.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).contDiff).mul
      (hh.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).contDiff))

theorem enorm_iteratedFDeriv_proj_comp_le {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : Fin 3)
    (x : Fin 3 → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (F ∘ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) r)
      x‖ₑ ≤ ‖iteratedDeriv m F (x r)‖ₑ := by
  refine (enorm_iteratedFDeriv_comp_le hF _ (norm_proj_le r) x m).trans_eq ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rfl

/-- **Leibniz rule for products of functions of three forms.** -/
theorem enorm_iteratedFDeriv_prod3_le {f g h : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (c : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ c (prod3 f g h) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * ‖iteratedDeriv j f (x 0)‖ₑ *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * ‖iteratedDeriv i g (x 1)‖ₑ *
          ‖iteratedDeriv (c - j - i) h (x 2)‖ₑ := by
  set P0 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0
  set P1 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1
  set P2 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2
  have h0 : ContDiff ℝ ∞ (f ∘ P0) := hf.comp P0.contDiff
  have h1 : ContDiff ℝ ∞ (g ∘ P1) := hg.comp P1.contDiff
  have h2 : ContDiff ℝ ∞ (h ∘ P2) := hh.comp P2.contDiff
  have h12 : ContDiff ℝ ∞ fun x => (g ∘ P1) x * (h ∘ P2) x := h1.mul h2
  have e : prod3 f g h = fun x => (f ∘ P0) x * (fun x => (g ∘ P1) x * (h ∘ P2) x) x := rfl
  rw [e]
  refine (enorm_iteratedFDeriv_mul_le h0 h12 x c).trans (Finset.sum_le_sum fun j _ => ?_)
  refine mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedFDeriv_proj_comp_le hf 0 x j)) ?_
  refine (enorm_iteratedFDeriv_mul_le h1 h2 x (c - j)).trans (Finset.sum_le_sum fun i _ => ?_)
  exact mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedFDeriv_proj_comp_le hg 1 x i))
    (enorm_iteratedFDeriv_proj_comp_le hh 2 x (c - j - i))

end Prod3

end WaveTurbulence.ClassJR
