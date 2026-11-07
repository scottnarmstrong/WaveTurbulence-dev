/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.FreeSum
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Assembly
/-! FLOWER-P7: the norm of `coupleSum … L0 false` is bounded by the summed piece bounds (outer-label sum of the
root-time integrals; the pointwise-in-time bound is the one of the `dt = true` case with the per-tree caps
`s_{j(c)}`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset MeasureTheory

theorem sum_toFinset_Y6 (P : WTParams) (p N : ℕ) (kind : TreeKind) (f : LayeredGarden (2 * 3) → ℂ) :
    ∑ y ∈ (finite_Y6 P p N kind).toFinset, f y.1 = ∑ᶠ y ∈ Y6Set P p N kind, f y := by
  rw [← finsum_capSrc_eq P p N kind f]
  rw [show (∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N kind y.1), f y.1) =
    ∑ᶠ y ∈ {y : CapSrc p | Y6Cond P p N kind y.1}, f y.1 from rfl,
    finsum_mem_eq_finite_toFinset_sum _ (finite_Y6 P p N kind)]

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ} {Cr : ℝ}

theorem norm_freeIntegrand_sum_le
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr) (t : ℝ) (n : OuterLabels P.d) (s : Fin 2 → ℝ) :
    ‖∑ y ∈ (finite_Y6 P p N .L0).toFinset, freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s‖ ≤
      (rootDom p t).indicator (fun _ => Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
        Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1) s := by
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs]
    have h1 : ∑ y ∈ (finite_Y6 P p N .L0).toFinset, freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s =
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
          rootPhaseS P.L P.γ P.δ k s n.1 *
          ∑ᶠ y ∈ Y6Set P p N .L0, kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1)
            (fun b => s (jOf b.1.1)) k n.1 0 := by
      rw [← sum_toFinset_Y6, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold freeIntegrand
      rw [Set.indicator_of_mem hs]
    rw [h1, norm_mul, norm_mul, norm_rootPhaseS, mul_one]
    have he : ‖((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => abs_epsCoef_le_one _ _ _)
    have htt : ∀ j, (fun c : Fin (2 * 3) => s (jOf c)) j ∈ Set.Icc (p : ℝ) (p + 1) := fun j =>
      ⟨(hs (jOf j)).1.le, (hs (jOf j)).2.1.le⟩
    have hY := Y6_sum_norm_le_Wtot (Hs _ htt) hb .L0 n.1
    calc ‖((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)‖ *
          ‖∑ᶠ y ∈ Y6Set P p N .L0, kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1)
            (fun b => s (jOf b.1.1)) k n.1 0‖
        ≤ 1 * (Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1) :=
          mul_le_mul he hY (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hs]
    have : ∀ y ∈ (finite_Y6 P p N .L0).toFinset,
        freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s = 0 := fun y _ => by
      unfold freeIntegrand; rw [Set.indicator_of_notMem hs]
    rw [Finset.sum_eq_zero this, norm_zero]

/-- **The decapitation bound for `kind = L0`, `dt = false`.** -/
theorem coupleSum_false_norm_le
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr) (t : ℝ) (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L n)|) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
        (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) *
          (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6))) := by
  rw [coupleSum_false_swap P (inputsF P Rr) p N t k hF, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hQ0 : 0 ≤ Qn P p N Cr := by linarith [Qn_pos P p N hb.hCr0]
  set g : OuterLabels P.d → ℝ := fun n => Qn P p N Cr * G * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (mul_nonneg hQ0 hG0) (Wtot_nonneg _ _ _ _)
  set B : ℝ := Qn P p N Cr * G * (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) *
    jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) * (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6)) with hB
  have hpart : ∀ u : Finset (OuterLabels P.d), ∑ n ∈ u, g n ≤ B := by
    intro u
    simp only [hg]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Wtot_sum_le hb.hL k hΛ u) (mul_nonneg hQ0 hG0)
  have hs : Summable g := summable_of_sum_le hg0 hpart
  refine (tsum_of_norm_bounded hs.hasSum fun n => ?_).trans (Real.tsum_le_of_sum_le hg0 hpart)
  have hmeas := measurableSet_rootDom p t
  have hI : Integrable ((rootDom p t).indicator fun _ => g n) :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const (volume_rootDom_lt_top p t).ne)
  calc ‖∫ s : Fin 2 → ℝ, ∑ y ∈ (finite_Y6 P p N .L0).toFinset,
          freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s‖
      ≤ ∫ s, (rootDom p t).indicator (fun _ => g n) s :=
        norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun s =>
          norm_freeIntegrand_sum_le Hs hb t n s)
    _ = (volume : Measure (Fin 2 → ℝ)).real (rootDom p t) * g n := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul]
    _ ≤ g n := mul_le_of_le_one_left (hg0 n) (volume_rootDom_le p t)

end

end WaveTurbulence.FlowerP7
