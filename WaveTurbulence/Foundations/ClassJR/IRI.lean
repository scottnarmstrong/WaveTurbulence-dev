/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma56

/-!
# DH21 Lemma 5.7, `I_{εα₁} ℛ I_{μ₁-εα₁}`: forms and the double integral

For a basic class `R` operator `∫ m(α', γ) χ_∞(ℓ₁+ε₂α₂+γ₃)/(ℓ₁+ε₂α₂+γ₃) J_{ℓ₂+ε₂α₂;γ₁,γ₂} dγ`
(special variable `α₂`), the two splittings of DH21 L1047–L1053 produce the forms
`x₀ = ℓ₂ + γ₁ + εα₁ + ε₂α₂`, `x₁ = γ₁ + γ₂ + εα₁` and the denominator `x₂ = ℓ₁ + γ₃ + ε₂α₂`
(DH21 L1066–L1072). The class `J` pieces carry a coupling `f(x₀) g(x₁) h(x₂)`; their weighted
integrals over `(α₁, α₂)` are bounded by `lintegral_prod3_IRI_le` through the triple decay
estimate `lintegral_tri3_le` of Lemma 5.5. The variables are `(ι ⊕ Empty) ⊕ Fin 2 → ℝ` with
`α₁ = α (inr 0)` and `α₂ = α (inr 1)`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Double

theorem sign_real_neg {e : ℝ} (he : e = 1 ∨ e = -1) : -e = 1 ∨ -e = -1 := by
  rcases he with rfl | rfl
  · right; rfl
  · left; norm_num

/-- `lintegral_tri3_le` for the sign pattern of Lemma 5.7 (`α₁` enters `x₀` and `x₁` with the
same sign). -/
theorem lintegral_tri3_IRI_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε ε₂ : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (X₀ X₁ X₂ : ℝ) :
    ∫⁻ s : Fin 2 → ℝ, ENNReal.ofReal
      (tri3 θ (X₀ + ε * s 0 + ε₂ * s 1) (X₁ + ε * s 0) (X₂ + ε₂ * s 1)) ≤
        ENNReal.ofReal (D3 θ) := by
  have e : ∀ s : Fin 2 → ℝ, tri3 θ (X₀ + ε * s 0 + ε₂ * s 1) (X₁ + ε * s 0) (X₂ + ε₂ * s 1) =
      tri3 θ (X₀ - -ε * s 0 + ε₂ * s 1) (-X₁ + -ε * s 0) (X₂ + ε₂ * s 1) := fun s => by
    unfold tri3
    rw [show -X₁ + -ε * s 0 = -(X₁ + ε * s 0) by ring, abs_neg,
      show X₀ - -ε * s 0 + ε₂ * s 1 = X₀ + ε * s 0 + ε₂ * s 1 by ring]
  simp_rw [e]
  exact lintegral_tri3_le h0 h1 (sign_real_neg hε) hε₂ X₀ (-X₁) X₂

/-- The Leibniz sum of the derivative constants of a product coupling. -/
@[expose] noncomputable def lsum3 (Ff Fg Fh : ℕ → ℝ≥0∞) (c : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * Ff j *
    ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * Fg i * Fh (c - j - i)

theorem enorm_iteratedFDeriv_prod3_le_rho {f g h : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) {a b : ℝ} {Ff Fg Fh : ℕ → ℝ≥0∞}
    (hFf : ∀ j y, ‖iteratedDeriv j f y‖ₑ ≤ Ff j * ENNReal.ofReal ((1 + |y - a|)⁻¹))
    (hFg : ∀ j y, ‖iteratedDeriv j g y‖ₑ ≤ Fg j * ENNReal.ofReal ((1 + |y - b|)⁻¹))
    (hFh : ∀ j y, ‖iteratedDeriv j h y‖ₑ ≤ Fh j * ENNReal.ofReal ((1 + |y|)⁻¹))
    (c : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ c (prod3 f g h) x‖ₑ ≤ lsum3 Ff Fg Fh c *
      (ENNReal.ofReal ((1 + |x 0 - a|)⁻¹) * ENNReal.ofReal ((1 + |x 1 - b|)⁻¹) *
        ENNReal.ofReal ((1 + |x 2|)⁻¹)) := by
  refine (enorm_iteratedFDeriv_prod3_le hf hg hh c x).trans ?_
  unfold lsum3
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc (c.choose j : ℝ≥0∞) * ‖iteratedDeriv j f (x 0)‖ₑ *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * ‖iteratedDeriv i g (x 1)‖ₑ *
          ‖iteratedDeriv (c - j - i) h (x 2)‖ₑ
      ≤ (c.choose j : ℝ≥0∞) * (Ff j * ENNReal.ofReal ((1 + |x 0 - a|)⁻¹)) *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) *
          (Fg i * ENNReal.ofReal ((1 + |x 1 - b|)⁻¹)) *
            (Fh (c - j - i) * ENNReal.ofReal ((1 + |x 2|)⁻¹)) := by
        gcongr with i hi
        · exact hFf j _
        · exact hFg i _
        · exact hFh _ _
    _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- **The weighted double integral of a product coupling** (DH21 L1066–L1072): if the three
factors decay like `(1+|y-a|)⁻¹`, `(1+|y-b|)⁻¹`, `(1+|y|)⁻¹` with derivative constants `F`, then
the integral over `(α₁, α₂)` of `V ‖∂^c (f ⊗ g ⊗ h)‖` is at most `D3 θ` times the Leibniz sum. -/
theorem lintegral_prod3_IRI_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε ε₂ : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {f g h : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) {a b : ℝ} {Ff Fg Fh : ℕ → ℝ≥0∞}
    (hFf : ∀ j y, ‖iteratedDeriv j f y‖ₑ ≤ Ff j * ENNReal.ofReal ((1 + |y - a|)⁻¹))
    (hFg : ∀ j y, ‖iteratedDeriv j g y‖ₑ ≤ Fg j * ENNReal.ofReal ((1 + |y - b|)⁻¹))
    (hFh : ∀ j y, ‖iteratedDeriv j h y‖ₑ ≤ Fh j * ENNReal.ofReal ((1 + |y|)⁻¹))
    (X₀ X₁ X₂ : ℝ) (v : (Fin 2 → ℝ) → Fin 3 → ℝ)
    (hv0 : ∀ s, v s 0 = X₀ + ε * s 0 + ε₂ * s 1) (hv1 : ∀ s, v s 1 = X₁ + ε * s 0)
    (hv2 : ∀ s, v s 2 = X₂ + ε₂ * s 1) (c : ℕ) :
    ∫⁻ s, ((1 + ‖v s 0 - a‖ₑ) ^ θ + (1 + ‖v s 1 - b‖ₑ) ^ θ + (1 + ‖v s 2‖ₑ) ^ θ) *
      ‖iteratedFDeriv ℝ c (prod3 f g h) (v s)‖ₑ ≤
      ENNReal.ofReal (D3 θ) * lsum3 Ff Fg Fh c := by
  have hpt : ∀ s, ((1 + ‖v s 0 - a‖ₑ) ^ θ + (1 + ‖v s 1 - b‖ₑ) ^ θ + (1 + ‖v s 2‖ₑ) ^ θ) *
      ‖iteratedFDeriv ℝ c (prod3 f g h) (v s)‖ₑ ≤ lsum3 Ff Fg Fh c *
        ENNReal.ofReal (tri3 θ (X₀ - a + ε * s 0 + ε₂ * s 1) (X₁ - b + ε * s 0)
          (X₂ + ε₂ * s 1)) := fun s => by
    have e0 : v s 0 - a = X₀ - a + ε * s 0 + ε₂ * s 1 := by rw [hv0]; ring
    have e1 : v s 1 - b = X₁ - b + ε * s 0 := by rw [hv1]; ring
    refine (mul_le_mul' le_rfl (enorm_iteratedFDeriv_prod3_le_rho hf hg hh hFf hFg hFh c
      (v s))).trans_eq ?_
    rw [mul_left_comm, V_mul_rho_eq h0, e0, e1, hv2]
  have hm : Measurable fun s : Fin 2 → ℝ =>
      ENNReal.ofReal (tri3 θ (X₀ - a + ε * s 0 + ε₂ * s 1) (X₁ - b + ε * s 0) (X₂ + ε₂ * s 1)) := by
    unfold tri3; fun_prop
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul _ hm, mul_comm]
  exact mul_le_mul' (lintegral_tri3_IRI_le h0 h1 hε hε₂ _ _ _) le_rfl

end Double

section Forms

variable {ι : Type*} [Fintype ι]

/-- The forms `x₀ = ℓ₂ + γ₁ + εα₁ + ε₂α₂`, `x₁ = γ₁ + γ₂ + εα₁`, `x₂ = ℓ₁ + γ₃ + ε₂α₂`. -/
@[expose] def LsIRI (R : RSym ι) (ε : ℤ) : Fin 3 → (ι ⊕ Empty) ⊕ Fin 2 → ℤ :=
  ![y4 R.y₂ 0 ε R.ε, y4 0 0 ε 0, y4 R.y₁ 0 0 R.ε]

/-- The constant parts `γ₁`, `γ₁ + γ₂`, `γ₃`. -/
@[expose] def csIRI (Q : Type*) : Fin 3 → (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ :=
  ![fun z => z.1.1, fun z => z.1.1 + z.1.2.1, fun z => z.1.2.2]

theorem isBundle_LsIRI {R : RSym ι} {θ A N : ℝ} (h : R.Bound θ A N) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : ∀ r, IsBundle (LsIRI R ε r) := by
  intro r; fin_cases r
  · exact isBundle_y4 h.bundle₂ isBundle_zero (abs_sign_le hε) (abs_sign_le h.sign)
  · exact isBundle_y4 isBundle_zero isBundle_zero (abs_sign_le hε) (by simp)
  · exact isBundle_y4 h.bundle₁ isBundle_zero (by simp) (abs_sign_le h.sign)

theorem measurable_csIRI (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csIRI Q r) := by
  intro r; fin_cases r
  · simp only [csIRI]; exact measurable_fst.comp measurable_fst
  · simp only [csIRI]
    exact (measurable_fst.comp measurable_fst).add
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  · simp only [csIRI]; exact measurable_snd.comp (measurable_snd.comp measurable_fst)

variable {R : RSym ι} {ε : ℤ} {Q : Type*}

theorem formsV_IRI_zero (α : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRI R ε) (csIRI Q) α z 0 =
      bundle R.y₂ (vA α) + z.1.1 + ε * α (Sum.inr 0) + R.ε * α (Sum.inr 1) := by
  simp only [formsV, LsIRI, csIRI, Matrix.cons_val, bundle_y4, bundle_zero_fun]
  ring

theorem formsV_IRI_one (α : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRI R ε) (csIRI Q) α z 1 = z.1.1 + z.1.2.1 + ε * α (Sum.inr 0) := by
  simp only [formsV, LsIRI, csIRI, Matrix.cons_val, bundle_y4, bundle_zero_fun]
  push_cast
  ring

theorem formsV_IRI_two (α : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRI R ε) (csIRI Q) α z 2 = bundle R.y₁ (vA α) + z.1.2.2 + R.ε * α (Sum.inr 1) := by
  simp only [formsV, LsIRI, csIRI, Matrix.cons_val, bundle_y4, bundle_zero_fun]
  push_cast
  ring

end Forms

end WaveTurbulence.ClassJR
