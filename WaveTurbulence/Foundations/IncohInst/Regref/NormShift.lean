/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Translate

/-!
# The `𝔛` norms are invariant under translating time

Translating the time variables by `c` multiplies the time Fourier transform by the unimodular factor
`e^{-2πi⟨λ, c⟩}` (`timeFT_shift`); momentum derivatives commute with this constant factor (`iterPartial_const_mul`).
Hence `‖F(· − c)‖_{𝔛^{θ,Λ₁,Λ₂}} = ‖F‖_{𝔛^{θ,Λ₁,Λ₂}}` (`XNorm_shift`), the same for `𝔛^{θ,0,0}` (`XNorm00_shift`),
and the restriction norms on a box translated by `c` are bounded by those on the box (`XNormRestr_shift_le`,
`XNorm00Restr_shift_le`). Used for the layer shift `r ↦ 0` of TARGET L1173.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Regref

variable {d : ℕ}

theorem timeFT_shift {r : ℕ} {V : Type*} (F : (Fin r → ℝ) → V → ℂ) (c lam : Fin r → ℝ) (v : V) :
    timeFT (fun t v => F (t - c) v) lam v =
      Complex.exp (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) * Complex.I) * timeFT F lam v := by
  unfold timeFT
  have h := integral_sub_right_eq_self (μ := (volume : Measure (Fin r → ℝ)))
    (fun t => F t v * Complex.exp (-(2 * Real.pi * ∑ i, lam i * (t + c) i : ℝ) * Complex.I)) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [Complex.ofReal_add, neg_add, add_mul, Complex.exp_add]
  ring

theorem norm_exp_ofReal_mul_I' (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem partialMom_const_mul (j : Fin d) (u : ℂ) (f : Mom d → ℂ) :
    partialMom j (fun k => u * f k) = fun k => u * partialMom j f k := by
  funext k
  unfold partialMom
  by_cases hf : DifferentiableAt ℝ f k
  · rw [fderiv_const_mul hf]
    rfl
  · by_cases hu : u = 0
    · simp [hu]
    · have hf' : ¬ DifferentiableAt ℝ (fun k => u * f k) k := fun h => hf (by
        have := h.const_mul u⁻¹
        simpa [← mul_assoc, inv_mul_cancel₀ hu] using this)
      rw [fderiv_zero_of_not_differentiableAt hf', fderiv_zero_of_not_differentiableAt hf]
      simp

theorem iterate_partialMom_const_mul (j : Fin d) (u : ℂ) : (m : ℕ) → (f : Mom d → ℂ) →
    (partialMom j)^[m] (fun k => u * f k) = fun k => u * (partialMom j)^[m] f k
  | 0, f => rfl
  | m + 1, f => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_partialMom_const_mul j u m f,
      partialMom_const_mul]

theorem iterPartial_const_mul (ρ : Fin d → ℕ) (u : ℂ) (f : Mom d → ℂ) :
    iterPartial ρ (fun k => u * f k) = fun k => u * iterPartial ρ f k := by
  unfold iterPartial
  induction (List.finRange d) with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_partialMom_const_mul]

theorem contDiff_const_mul_iff {n : ℕ} {u : ℂ} (hu : u ≠ 0) (f : Mom d → ℂ) :
    ContDiff ℝ n (fun k => u * f k) ↔ ContDiff ℝ n f := by
  constructor
  · intro h
    have := (contDiff_const (c := u⁻¹)).mul h
    simpa [← mul_assoc, inv_mul_cancel₀ hu] using this
  · intro h
    exact contDiff_const.mul h

theorem integrable_shift_iff {r : ℕ} (g : (Fin r → ℝ) → ℂ) (c : Fin r → ℝ) :
    Integrable (fun t => g (t - c)) ↔ Integrable g := by
  constructor
  · intro h
    have := h.comp_add_right c
    simpa using this
  · intro h
    exact h.comp_sub_right c

/-- **`𝔛^{θ,Λ₁,Λ₂}` is invariant under time translation.** -/
theorem XNorm_shift {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) (c : Fin r → ℝ) :
    XNorm θ Λ₁ Λ₂ (fun t k => F (t - c) k) = XNorm θ Λ₁ Λ₂ F := by
  unfold XNorm
  have hint : (∀ k, Integrable fun t => F (t - c) k) ↔ ∀ k, Integrable fun t => F t k :=
    forall_congr' fun k => integrable_shift_iff (fun t => F t k) c
  have hcd : (∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT (fun t k => F (t - c) k) lam)) ↔
      ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam) := by
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun lam => ?_)
    set u : ℂ := Complex.exp (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) * Complex.I) with hu
    have hu0 : u ≠ 0 := Complex.exp_ne_zero _
    have hft : timeFT (fun t k => F (t - c) k) lam = fun k => u * timeFT F lam k :=
      funext fun k => timeFT_shift F c lam k
    rw [hft, contDiff_const_mul_iff hu0]
  have hg : ((∀ k, Integrable fun t => F (t - c) k) ∧
      (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT (fun t k => F (t - c) k) lam))) ↔
      ((∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))) := by
    rw [hint, hcd]
  by_cases hI : (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))
  · rw [ite_eq_left (hg.2 hI), ite_eq_left hI]
    refine iSup_congr fun ρ => iSup_congr fun _ => lintegral_congr fun lam => ?_
    set u : ℂ := Complex.exp (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) * Complex.I) with hu
    have hu1 : ‖u‖ = 1 := by rw [hu, show (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) : ℂ) = ((-(2 * Real.pi *
      ∑ i, lam i * c i) : ℝ) : ℂ) by push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
    have hft : timeFT (fun t k => F (t - c) k) lam = fun k => u * timeFT F lam k :=
      funext fun k => timeFT_shift F c lam k
    rw [hft, iterPartial_const_mul]
    congr 1
    refine iSup_congr fun k => ?_
    rw [norm_mul, hu1, one_mul]
  · rw [ite_eq_right (fun h => hI (hg.1 h)), ite_eq_right hI]

/-- **Restriction norms under translation**: if `F' = F(· − c)` on `B'` and `B' − c ⊆ B`, then
`‖F'‖_{𝔛(B')} ≤ ‖F‖_{𝔛(B)}`. -/
theorem XNormRestr_shift_le {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) {B B' : Set (Fin r → ℝ)} {K : Set (Mom d)}
    {F F' : (Fin r → ℝ) → Mom d → ℂ} (c : Fin r → ℝ) (hB : ∀ t ∈ B', t - c ∈ B)
    (hF : ∀ t ∈ B', ∀ k ∈ K, F' t k = F (t - c) k) :
    XNormRestr θ Λ₁ Λ₂ B' K F' ≤ XNormRestr θ Λ₁ Λ₂ B K F := by
  unfold XNormRestr
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t k => G (t - c) k) fun t ht k hk => ?_).trans (XNorm_shift θ Λ₁ Λ₂ G c).le
  show G (t - c) k = F' t k
  rw [hG _ (hB t ht) k hk, hF t ht k hk]

/-- **`𝔛^{θ,0,0}` is invariant under time translation.** -/
theorem XNorm00_shift {r : ℕ} {V : Type*} (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) (c : Fin r → ℝ) :
    XNorm00 θ (fun t v => F (t - c) v) = XNorm00 θ F := by
  unfold XNorm00
  have hint : (∀ v, Integrable fun t => F (t - c) v) ↔ ∀ v, Integrable fun t => F t v :=
    forall_congr' fun v => integrable_shift_iff (fun t => F t v) c
  by_cases hI : ∀ v, Integrable fun t => F t v
  · rw [ite_eq_left (hint.2 hI), ite_eq_left hI]
    refine lintegral_congr fun lam => ?_
    congr 1
    refine iSup_congr fun v => ?_
    rw [timeFT_shift, enorm_mul]
    rw [show (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) : ℂ) = ((-(2 * Real.pi *
      ∑ i, lam i * c i) : ℝ) : ℂ) by push_cast; ring]
    rw [← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one, one_mul]
  · rw [ite_eq_right (fun h => hI (hint.1 h)), ite_eq_right hI]

theorem XNorm00Restr_shift_le {r : ℕ} {V : Type*} (θ : ℝ) {B B' : Set (Fin r → ℝ)} {K : Set V}
    {F F' : (Fin r → ℝ) → V → ℂ} (c : Fin r → ℝ) (hB : ∀ t ∈ B', t - c ∈ B)
    (hF : ∀ t ∈ B', ∀ v ∈ K, F' t v = F (t - c) v) :
    XNorm00Restr θ B' K F' ≤ XNorm00Restr θ B K F := by
  unfold XNorm00Restr
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t v => G (t - c) v) fun t ht v hv => ?_).trans (XNorm00_shift θ G c).le
  show G (t - c) v = F' t v
  rw [hG _ (hB t ht) v hv, hF t ht v hv]

end WaveTurbulence.Regref
