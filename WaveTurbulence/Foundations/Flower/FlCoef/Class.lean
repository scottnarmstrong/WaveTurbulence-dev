/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FlCoef.Mul

/-!
# FL-COEF: closure of classes `J` and `R` under multiplication by cutoff products

Supplement Lemma 8.1 (first estimate of (8.3)) in main's normalization: `ClassJ θ A N` and
`ClassR θ A N` are closed under multiplication by `∏ᵢ χ₀(α_{c i}/S_i)`, `S_i ≥ 1`, at most two
factors per coordinate, with the same radius `A ≥ A₀` and a constant `4 (4e⁴)^{2|ι|} N` independent
of the scales `S`.
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.Flower.FlCoef

open WaveTurbulence.ClassJR MeasureTheory Finset
open scoped ContDiff ENNReal

variable {ι : Type*} [Fintype ι]

theorem measurable_wJ (θ : ℝ) :
    Measurable (Function.uncurry fun (α : ι → ℝ) (γ : ℝ × ℝ) => wJ θ α γ.1) := by
  unfold wJ
  fun_prop

theorem measurable_wR (θ : ℝ) :
    Measurable (Function.uncurry fun (α : ι → ℝ) (γ : ℝ × ℝ × ℝ) => wR θ α γ.1 γ.2.2) := by
  unfold wR
  fun_prop

section J

/-- Multiplying the symbol of a basic class `J` operator by `F`. -/
def jsymMulF (F : (ι → ℝ) → ℂ) (R : JSym ι) : JSym ι := ⟨R.y, mulSym F R.m⟩

theorem jsym_kernel_mulF (F : (ι → ℝ) → ℂ) (R : JSym ι) (α : ι → ℝ) (t s : ℝ) :
    (jsymMulF F R).kernel α t s = F α * R.kernel α t s := by
  unfold JSym.kernel jsymMulF mulSym
  simp only
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun γ => by ring)

theorem jsymBound_mulF {F : (ι → ℝ) → ℂ} {NF A θ N : ℝ} {R : JSym ι}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev NF A k) (hNF : 0 ≤ NF) (hA : 0 ≤ A)
    (hR : R.Bound θ A N) : (jsymMulF F R).Bound θ A (4 * NF * N) where
  nonneg := by have := hR.nonneg; positivity
  bundle := hR.bundle
  reg := symReg_mulSym hF hFb hR.reg
  norm k := by
    have h1 := lintegral_dnorm_mulSym_le hF hFb hR.reg.smooth hR.reg.meas
      (fun α (γ : ℝ × ℝ) => wJ θ α γ.1) (measurable_wJ θ) k
    refine h1.trans ?_
    exact gev_conv_le (S₁ := fun j => gev NF A j) (S₂ := fun j => jNorm θ j R.m) hNF hR.nonneg hA
      (fun j => le_rfl) hR.norm k

/-- **FL-COEF for class `J`.** Multiplication by a Gevrey-2 multiplier preserves class `J`, with the
same radius and the norm multiplied by `4 N_F`. -/
theorem classJ_mulF {F : (ι → ℝ) → ℂ} {NF A θ N : ℝ} {T : (ι → ℝ) → ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev NF A k) (hNF : 0 ≤ NF) (hA : 0 ≤ A)
    (hT : ClassJ θ A N T) : ClassJ θ A (4 * NF * N) (fun α t s => F α * T α t s) := by
  obtain ⟨n, R, c, hb, hsum, hker⟩ := hT
  refine ⟨n, fun i => jsymMulF F (R i), fun i => 4 * NF * c i, fun i =>
    jsymBound_mulF hF hFb hNF hA (hb i), ?_, fun α t s ht hst h1 => ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · simp only [jsym_kernel_mulF]
    rw [hker α t s ht hst h1, Finset.mul_sum]

end J

section R

/-- Multiplying the symbol of a basic class `R` operator by `F` (a function of the non-special
variables). -/
def rsymMulF (F : (ι → ℝ) → ℂ) (R : RSym ι) : RSym ι :=
  ⟨R.ε, R.y₁, R.y₂, mulSym F R.m⟩

theorem rsym_kernel_mulF (F : (ι → ℝ) → ℂ) (R : RSym ι) (α : Option ι → ℝ) (t s : ℝ) :
    (rsymMulF F R).kernel α t s = F (nsp α) * R.kernel α t s := by
  unfold RSym.kernel rsymMulF mulSym
  simp only
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun γ => by ring)

theorem rsymBound_mulF {F : (ι → ℝ) → ℂ} {NF A θ N : ℝ} {R : RSym ι}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev NF A k) (hNF : 0 ≤ NF) (hA : 0 ≤ A)
    (hR : R.Bound θ A N) : (rsymMulF F R).Bound θ A (4 * NF * N) where
  nonneg := by have := hR.nonneg; positivity
  sign := hR.sign
  bundle₁ := hR.bundle₁
  bundle₂ := hR.bundle₂
  reg := symReg_mulSym hF hFb hR.reg
  norm k := by
    have h1 := lintegral_dnorm_mulSym_le hF hFb hR.reg.smooth hR.reg.meas
      (fun α (γ : ℝ × ℝ × ℝ) => wR θ α γ.1 γ.2.2) (measurable_wR θ) k
    refine h1.trans ?_
    exact gev_conv_le (S₁ := fun j => gev NF A j) (S₂ := fun j => rNorm θ j R.m) hNF hR.nonneg hA
      (fun j => le_rfl) hR.norm k

/-- **FL-COEF for class `R`.** The multiplier is a function of the non-special variables. -/
theorem classR_mulF {F : (ι → ℝ) → ℂ} {NF A θ N : ℝ} {T : (Option ι → ℝ) → ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFb : ∀ k α, FD k F α ≤ gev NF A k) (hNF : 0 ≤ NF) (hA : 0 ≤ A)
    (hT : ClassR θ A N T) :
    ClassR θ A (4 * NF * N) (fun α t s => F (nsp α) * T α t s) := by
  obtain ⟨n, R, c, hb, hsum, hker⟩ := hT
  refine ⟨n, fun i => rsymMulF F (R i), fun i => 4 * NF * c i, fun i =>
    rsymBound_mulF hF hFb hNF hA (hb i), ?_, fun α t s ht hst h1 => ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · simp only [rsym_kernel_mulF]
    rw [hker α t s ht hst h1, Finset.mul_sum]

end R

section Cutoffs

variable {κ : Type*} [Fintype κ]

theorem FD_cutProd_le (c : κ → ι) (S : κ → ℝ) (hS : ∀ i, 1 ≤ S i) {A : ℝ} (hA : chiA ≤ A)
    (k : ℕ) (α : ι → ℝ) :
    FD k (cutProd c S) α ≤ gev ((4 * Real.exp 4) ^ Fintype.card κ) A k := by
  classical
  exact (enorm_iteratedFDeriv_cutProd_le c S hS k α).trans
    (gev_mono le_rfl chiA_nonneg hA (by positivity) k)

theorem card_le_two_mul (c : κ → ι) (h2 : ∀ j, Nat.card {i // c i = j} ≤ 2) :
    Fintype.card κ ≤ 2 * Fintype.card ι := by
  classical
  calc Fintype.card κ = ∑ j, (univ.filter fun i => c i = j).card := by
        rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := c)
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    _ ≤ ∑ _j : ι, 2 := Finset.sum_le_sum fun j _ => by
        have := h2 j
        rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    _ = 2 * Fintype.card ι := by simp [mul_comm]

theorem one_le_four_exp : (1 : ℝ) ≤ 4 * Real.exp 4 := by
  have := Real.add_one_le_exp 4
  linarith

/-- **FL-COEF (Lemma 8.1, class `J`).** Let `T` have class `J` with norm at most `N` and
radius `A ≥ A₀ = 16 + 16 e²` (the Gevrey radius of `χ₀`). Multiply by `∏ᵢ χ₀(α_{c i}/S_i)`, with
every `S_i ≥ 1` and at most two factors per coordinate. Then the product has class `J` with the same
`θ`, the same radius `A`, and norm at most `4 (4e⁴)^{2|ι|} N`, independent of the scales `S`. -/
theorem classJ_mul_cutProd {A θ N : ℝ} {T : (ι → ℝ) → ℝ → ℝ → ℂ} (c : κ → ι) (S : κ → ℝ)
    (hS : ∀ i, 1 ≤ S i) (h2 : ∀ j, Nat.card {i // c i = j} ≤ 2) (hA : chiA ≤ A)
    (hT : ClassJ θ A N T) :
    ClassJ θ A (4 * (4 * Real.exp 4) ^ (2 * Fintype.card ι) * N)
      (fun α t s => cutProd c S α * T α t s) := by
  have h := classJ_mulF (contDiff_cutProd c S) (FD_cutProd_le c S hS hA)
    (by positivity : 0 ≤ (4 * Real.exp 4) ^ Fintype.card κ) (chiA_nonneg.trans hA) hT
  obtain ⟨n, R, cc, hb, hsum, hker⟩ := h
  refine ⟨n, R, cc, hb, hsum.trans ?_, hker⟩
  have hN : 0 ≤ N := by
    obtain ⟨n, R, cc, hb, hsum, _⟩ := hT
    exact (Finset.sum_nonneg fun i _ => (hb i).nonneg).trans hsum
  have hp := pow_le_pow_right₀ one_le_four_exp (card_le_two_mul c h2)
  gcongr

/-- **FL-COEF (Lemma 8.1, class `R`).** As `ClassJ.mul_cutProd`, with the cutoffs acting on the
non-special variables. -/
theorem classR_mul_cutProd {A θ N : ℝ} {T : (Option ι → ℝ) → ℝ → ℝ → ℂ} (c : κ → ι) (S : κ → ℝ)
    (hS : ∀ i, 1 ≤ S i) (h2 : ∀ j, Nat.card {i // c i = j} ≤ 2) (hA : chiA ≤ A)
    (hT : ClassR θ A N T) :
    ClassR θ A (4 * (4 * Real.exp 4) ^ (2 * Fintype.card ι) * N)
      (fun α t s => cutProd c S (nsp α) * T α t s) := by
  have h := classR_mulF (contDiff_cutProd c S) (FD_cutProd_le c S hS hA)
    (by positivity : 0 ≤ (4 * Real.exp 4) ^ Fintype.card κ) (chiA_nonneg.trans hA) hT
  obtain ⟨n, R, cc, hb, hsum, hker⟩ := h
  refine ⟨n, R, cc, hb, hsum.trans ?_, hker⟩
  have hN : 0 ≤ N := by
    obtain ⟨n, R, cc, hb, hsum, _⟩ := hT
    exact (Finset.sum_nonneg fun i _ => (hb i).nonneg).trans hsum
  have hp := pow_le_pow_right₀ one_le_four_exp (card_le_two_mul c h2)
  gcongr

end Cutoffs

end WaveTurbulence.Flower.FlCoef
