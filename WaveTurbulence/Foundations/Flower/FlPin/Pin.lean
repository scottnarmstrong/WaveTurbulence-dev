/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# FL-PIN: supplement Lemma 7.2

The terminal-pin identity on simplex time integrals: pinning the last time of the chain
`t > t₁ > ⋯ > t_n > a` by a Dirac mass at `s` gives `1_{a<s<t}` times the integral over
`t > t₁ > ⋯ > t_{n-1} > s`, with the pinned phase factor.  The translation statement
(phase `e^{π i q Σ β}`, equal to `1` when `Σ β = 0`) is also provided.
-/

@[expose] public section

open MeasureTheory Complex

namespace WaveTurbulence.Flower.FlPin

/-- The open simplex `t > x₀ > x₁ > ⋯ > x_{n-1} > a`. -/
def chainSet {n : ℕ} (t a : ℝ) (x : Fin n → ℝ) : Prop :=
  StrictAnti (Fin.cons t x : Fin (n + 1) → ℝ) ∧ ∀ i, a < x i

/-- The linked phase `exp (π i Σ β_ℓ x_ℓ)`. -/
noncomputable def chainPhase {n : ℕ} (β x : Fin n → ℝ) : ℂ :=
  Complex.exp (↑Real.pi * Complex.I * ↑(∑ i, β i * x i))

lemma strictAnti_snoc_iff {m : ℕ} (y : Fin (m + 1) → ℝ) (s : ℝ) :
    StrictAnti (Fin.snoc y s : Fin (m + 2) → ℝ) ↔ StrictAnti y ∧ ∀ i, s < y i := by
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · have := h.comp_strictMono (Fin.strictMono_castSucc (n := m + 1))
      simpa [Function.comp_def] using this
    · have := h (Fin.castSucc_lt_last i)
      simpa using this
  · rintro ⟨h1, h2⟩ i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i => simpa using h2 i
    | cast j =>
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr
        (hij.trans (Fin.castSucc_lt_last j)).ne
      simpa using h1 (by simpa using hij)

lemma chainSet_snoc {k : ℕ} (t a s : ℝ) (x : Fin k → ℝ) :
    chainSet t a (Fin.snoc x s : Fin (k + 1) → ℝ) ↔ a < s ∧ s < t ∧ chainSet t s x := by
  have hc : (Fin.cons t (Fin.snoc x s : Fin (k + 1) → ℝ) : Fin (k + 2) → ℝ)
      = Fin.snoc (Fin.cons t x : Fin (k + 1) → ℝ) s := by
    exact Fin.cons_snoc_eq_snoc_cons ..
  unfold chainSet
  rw [hc, strictAnti_snoc_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨by simpa using h3 (Fin.last k), ?_, h1, fun i => by simpa using h2 i.succ⟩
    simpa using h2 0
  · rintro ⟨has, hst, h1, h3⟩
    refine ⟨⟨h1, fun i => ?_⟩, fun i => ?_⟩
    · induction i using Fin.cases with
      | zero => simpa using hst
      | succ i => simpa using h3 i
    · induction i using Fin.lastCases with
      | last => simpa using has
      | cast i => simpa using (has.trans (h3 i))

/-- **Lemma 7.2** (terminal pin).  Pinning the last time at `s` by a Dirac mass. -/
theorem pin_identity {k : ℕ} (t a s : ℝ) (β : Fin (k + 1) → ℝ) :
    ∫ p : (Fin k → ℝ) × ℝ,
        (open Classical in
          if chainSet t a (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) then
            chainPhase β (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) else 0)
      ∂(volume.prod (Measure.dirac s))
    = (open Classical in if a < s ∧ s < t then
        Complex.exp (↑Real.pi * Complex.I * ↑(β (Fin.last k) * s)) else 0) *
      ∫ x : Fin k → ℝ,
        (open Classical in
          if chainSet t s x then chainPhase (fun i => β (Fin.castSucc i)) x else 0) := by
  classical
  rw [Measure.prod_dirac]
  have hme : MeasurableEmbedding (fun x : Fin k → ℝ => (x, s)) :=
    measurableEmbedding_prod_mk_right s
  rw [hme.integral_map]
  by_cases h : a < s ∧ s < t
  · rw [if_pos h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have key : chainSet t a (Fin.snoc x s : Fin (k + 1) → ℝ) ↔ chainSet t s x := by
      rw [chainSet_snoc]; exact ⟨fun h' => h'.2.2, fun h' => ⟨h.1, h.2, h'⟩⟩
    beta_reduce
    by_cases hx : chainSet t s x
    · rw [if_pos (key.2 hx), if_pos hx]
      unfold chainPhase
      rw [← Complex.exp_add]
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      congr 1
      push_cast
      ring
    · rw [if_neg (fun h' => hx (key.1 h')), if_neg hx, mul_zero]
  · rw [if_neg h, zero_mul]
    have : ∀ x : Fin k → ℝ, ¬ chainSet t a (Fin.snoc x s : Fin (k + 1) → ℝ) := by
      intro x hx
      rw [chainSet_snoc] at hx
      exact h ⟨hx.1, hx.2.1⟩
    simp only [this, if_false, integral_zero]

/-- The simplex integral of the linked phase over `t > x₀ > ⋯ > x_{n-1} > a`. -/
noncomputable def chainIntegral {n : ℕ} (t a : ℝ) (β : Fin n → ℝ) : ℂ :=
  open Classical in ∫ x : Fin n → ℝ, if chainSet t a x then chainPhase β x else 0

lemma chainSet_add_const {n : ℕ} (t a q : ℝ) (y : Fin n → ℝ) :
    chainSet t a (fun i => y i + q) ↔ chainSet (t - q) (a - q) y := by
  have hc : (Fin.cons t (fun i => y i + q) : Fin (n + 1) → ℝ)
      = fun i => (Fin.cons (t - q) y : Fin (n + 1) → ℝ) i + q := by
    funext i
    induction i using Fin.cases <;> simp
  unfold chainSet
  rw [hc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => by linarith [h2 i]⟩
    have := h1 hij
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => by linarith [h2 i]⟩
    have := h1 hij
    linarith

lemma chainPhase_add_const {n : ℕ} (β y : Fin n → ℝ) (q : ℝ) :
    chainPhase β (fun i => y i + q) =
      Complex.exp (↑Real.pi * Complex.I * ↑(q * ∑ i, β i)) * chainPhase β y := by
  unfold chainPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  simp only [mul_comm (q : ℂ)]
  ring

/-- **Lemma 7.2, translation**: translating the chain by `q` multiplies the integral by the
explicit phase `e^{π i q Σ β}`. -/
theorem chainIntegral_translate {n : ℕ} (t a q : ℝ) (β : Fin n → ℝ) :
    chainIntegral t a β =
      Complex.exp (↑Real.pi * Complex.I * ↑(q * ∑ i, β i)) *
        chainIntegral (t - q) (a - q) β := by
  classical
  unfold chainIntegral
  have h1 := integral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
    (fun x : Fin n → ℝ => (if chainSet t a x then chainPhase β x else (0 : ℂ)))
    (fun _ : Fin n => q)
  rw [← h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  have e : (y + fun _ => q) = fun i => y i + q := rfl
  rw [e]
  by_cases hy : chainSet (t - q) (a - q) y
  · rw [if_pos ((chainSet_add_const t a q y).2 hy), if_pos hy, chainPhase_add_const]
  · rw [if_neg (fun h' => hy ((chainSet_add_const t a q y).1 h')), if_neg hy, mul_zero]

/-- If the linked frequencies are paired by a fixed-point-free involution with opposite
values, then `Σ β = 0` and the translation phase is `1`. -/
theorem sum_eq_zero_of_pairing {n : ℕ} (β : Fin n → ℝ) (σ : Fin n → Fin n)
    (hσ : ∀ i, σ (σ i) = i) (hne : ∀ i, σ i ≠ i) (hβ : ∀ i, β (σ i) = -β i) :
    ∑ i, β i = 0 := by
  refine Finset.sum_involution (fun i _ => σ i) (fun i _ => ?_) (fun i _ _ => ?_)
    (fun i _ => Finset.mem_univ _) (fun i _ => hσ i)
  · rw [hβ]; ring
  · exact fun h => hne i h

/-- With all pairs present the translation phase is `1`. -/
theorem chainIntegral_translate_of_sum_zero {n : ℕ} (t a q : ℝ) (β : Fin n → ℝ)
    (h : ∑ i, β i = 0) : chainIntegral t a β = chainIntegral (t - q) (a - q) β := by
  rw [chainIntegral_translate t a q β, h]; simp

end WaveTurbulence.Flower.FlPin
