/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.MixAlgebra
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The indicator of an affine lattice constraint is a character mixture of mass one (DEGEN-VINE)

For integer coefficients `c : VIdx → ℤ`, `h : Fin 4 → ℤ`, put `y(x, E) = ∑ᵥ cᵥ Xᵥ + ∑ₖ hₖ Eₖ`.  If `y` is a
lattice point `n / L`, then `1[y = 0] = ∫_{[0,1]^d} e^{2πi ⟨a, n⟩} da`, and `e^{2πi⟨a, n⟩} = e^{2πi L⟨a, y⟩}`
splits into the output scalar `u(a, E)` and the input character with frequencies `L cᵥ a`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence MeasureTheory

variable {d : ℕ}

/-- `∫_0^1 e^{2πi n t} dt = 1[n = 0]` for integers `n`. -/
theorem integral_fourierChar_unit (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (↑(2 * Real.pi * (t * n)) * Complex.I) =
      if n = 0 then 1 else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    have hc : (2 * Real.pi * n * Complex.I : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    have h2 : ∀ t : ℝ, Complex.exp (↑(2 * Real.pi * (t * n)) * Complex.I) =
        Complex.exp ((2 * Real.pi * n * Complex.I) * t) := fun t => by
      congr 1; push_cast; ring
    simp_rw [h2]
    rw [this]
    have h3 : Complex.exp (2 * Real.pi * n * Complex.I * (1 : ℝ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← this]; congr 1; push_cast; ring
    have h4 : Complex.exp (2 * Real.pi * n * Complex.I) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← this]; congr 1; ring
    simp [h4]


namespace CharMix
variable {S : SumintShape}

/-- The affine value `∑ᵥ cᵥ Xᵥ + ∑ₖ hₖ Eₖ`. -/
noncomputable def affVal (S : SumintShape) (L : ℝ) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ)
    (x : S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) : Mom d :=
  ∑ v, (c v : ℝ) • latticePoint L (x v) + ∑ k, (h k : ℝ) • E k

/-- The mixture representing the indicator of `affVal = 0`. -/
noncomputable def indicator (S : SumintShape) (d : ℕ) (L : ℝ) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ) :
    CharMix S d where
  α := Fin d → ℝ
  μ := Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)
  ζ := fun a v => (L * (c v : ℝ)) • (WithLp.toLp 2 a : Mom d)
  hζ := (continuous_pi fun v => (continuous_const (y := L * (c v : ℝ))).smul
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).measurable
  u := fun a E => (Real.fourierChar (L * inner ℝ (WithLp.toLp 2 a : Mom d) (∑ k, (h k : ℝ) • E k)) : ℂ)
  hu := fun E => by
    refine (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp ?_
    exact (continuous_const.mul ((PiLp.continuous_toLp 2 _).inner continuous_const)).measurable
  hu1 := fun a E => by simp

theorem mass_indicator (L : ℝ) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ) :
    (indicator S d L c h).mass = 1 := by
  unfold mass indicator
  simp [Measure.real, Measure.pi_univ]

/-- Pointwise: the integrand is a single exponential of the affine value. -/
theorem integrand_indicator (L : ℝ) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ) (E : Fin 4 → Mom d)
    (x : S.VIdx → Fin d → ℤ) (a : (indicator S d L c h).α) :
    (indicator S d L c h).u a E * charOf S L ((indicator S d L c h).ζ a) x =
      Complex.exp (↑(2 * Real.pi * (L * inner ℝ (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d)
        (affVal S L c h x E))) * Complex.I) := by
  unfold charOf indicator affVal
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  have e1 : ∑ v, inner ℝ ((L * (c v : ℝ)) • (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d))
      (latticePoint L (x v)) =
      L * inner ℝ (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d)
        (∑ v, (c v : ℝ) • latticePoint L (x v)) := by
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have e2 : (↑(2 * Real.pi * (L * inner ℝ (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d)
        (∑ k, (h k : ℝ) • E k))) * Complex.I : ℂ) +
      ∑ v, (↑(2 * Real.pi * inner ℝ ((L * (c v : ℝ)) • (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d))
        (latticePoint L (x v))) * Complex.I : ℂ) =
      ↑(2 * Real.pi * (L * inner ℝ (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d)
        (∑ v, (c v : ℝ) • latticePoint L (x v) + ∑ k, (h k : ℝ) • E k))) * Complex.I := by
    have e3 : ∑ v, (↑(2 * Real.pi * inner ℝ ((L * (c v : ℝ)) • (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d))
        (latticePoint L (x v))) * Complex.I : ℂ) =
        ↑(2 * Real.pi * (L * inner ℝ (WithLp.toLp 2 (show Fin d → ℝ from a) : Mom d)
          (∑ v, (c v : ℝ) • latticePoint L (x v)))) * Complex.I := by
      rw [← Finset.sum_mul, ← e1, Finset.mul_sum, Complex.ofReal_sum]
    rw [e3, inner_add_right, mul_add, mul_add]
    push_cast
    ring
  exact e2


/-- **The value of the indicator mixture.** -/
theorem val_indicator {L : ℝ} (hL : L ≠ 0) (c : S.VIdx → ℤ) (h : Fin 4 → ℤ) (E : Fin 4 → Mom d)
    (x : S.VIdx → Fin d → ℤ) (n : Fin d → ℤ) (hn : affVal S L c h x E = latticePoint L n) :
    (indicator S d L c h).val L E x = if n = 0 then 1 else 0 := by
  have hpt : ∀ a : Fin d → ℝ,
      Complex.exp (↑(2 * Real.pi * (L * inner ℝ (WithLp.toLp 2 a : Mom d) (affVal S L c h x E))) *
        Complex.I) = ∏ j, Complex.exp (↑(2 * Real.pi * (a j * (n j : ℤ))) * Complex.I) := by
    intro a
    rw [hn, ← Complex.exp_sum]
    congr 1
    have : L * inner ℝ (WithLp.toLp 2 a : Mom d) (latticePoint L n) = ∑ j, a j * (n j : ℝ) := by
      unfold latticePoint
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [this]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  unfold val
  have h1 : (fun a : (indicator S d L c h).α => (indicator S d L c h).u a E *
      charOf S L ((indicator S d L c h).ζ a) x) =
      fun a : Fin d → ℝ => ∏ j, Complex.exp (↑(2 * Real.pi * (a j * (n j : ℤ))) * Complex.I) := by
    funext a
    rw [integrand_indicator]
    exact hpt a
  rw [h1]
  change ∫ a : Fin d → ℝ, ∏ j, Complex.exp (↑(2 * Real.pi * (a j * (n j : ℤ))) * Complex.I)
    ∂(Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  rw [integral_fintype_prod_eq_prod (fun j (t : ℝ) =>
    Complex.exp (↑(2 * Real.pi * (t * (n j : ℤ))) * Complex.I))]
  simp_rw [integral_fourierChar_unit]
  by_cases hn0 : n = 0
  · simp [hn0]
  · have : ∃ j, n j ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hn0 (funext hcon)
    obtain ⟨j, hj⟩ := this
    rw [if_neg hn0]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

end CharMix
end WaveTurbulence.DegenVine
