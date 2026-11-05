/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GaussianMassMoments
public import WaveTurbulence.Foundations.XChain.SysDraft.API
public import WaveTurbulence.Foundations.MainGlue.LatticeSum
/-! All-order conditional product integrability follows from mass conservation and Gaussian data. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem solution_norm_sq_le_initial_mass {d : ℕ} {L γ δ T : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsASolution L γ δ T c a) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    ‖a t n‖ ^ 2 ≤ ∑' m, ‖c m‖ ^ 2 := by
  have hs := SysAPI.IsASolution.summable_norm hL ha ht
  have hn (m : Fin d → ℤ) : ‖a t m‖ ≤ ∑' m, ‖a t m‖ :=
    hs.le_tsum m (fun _ _ => norm_nonneg _)
  have hs2 : Summable fun m => ‖a t m‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => by
      nlinarith [mul_le_mul_of_nonneg_right (hn m) (norm_nonneg (a t m))])
      (hs.mul_left (∑' m, ‖a t m‖))
  exact (hs2.le_tsum n (fun _ _ => sq_nonneg _)).trans_eq
    (SysAPI.IsASolution.tsum_normSq_eq hL ha ht)

theorem solution_norm_le_one_add_gaussian_mass {d : ℕ} {Ω : Type*} {L γ δ T : ℝ}
    (hL : 0 < L) (φ : Mom d → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (g : (Fin d → ℤ) → Ω → ℂ) (ω : Ω) {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsASolution L γ δ T (initialCoeff L φ g ω) a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (n : Fin d → ℤ) : ‖a t n‖ ≤ 1 + ∑' m, φ (latticePoint L m) * ‖g m ω‖ ^ 2 := by
  have h := solution_norm_sq_le_initial_mass hL ha ht n
  have he : (∑' m, ‖initialCoeff L φ g ω m‖ ^ 2) =
      ∑' m, φ (latticePoint L m) * ‖g m ω‖ ^ 2 := by
    apply tsum_congr
    intro m
    rw [initialCoeff, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hφ _)]
  rw [he] at h
  have h0 : 0 ≤ ∑' m, φ (latticePoint L m) * ‖g m ω‖ ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (hφ _) (sq_nonneg _)
  nlinarith [norm_nonneg (a t n), sq_nonneg (‖a t n‖ - 1)]

/-- The all-order product integrability clause of AnsatzAt needs no additional gate. -/
theorem integrable_signed_prod_of_solutions {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L γ δ T : ℝ} (hL : 0 < L)
    (φ : SchwartzMap (Mom d) ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ)
    (F : Set Ω) (hF : MeasurableSet F) (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (r : ℕ) (t : Fin r → Icc (0 : ℝ) T) (n : Fin r → (Fin d → ℤ)) (ζ : Fin r → ℤˣ) :
    Integrable (fun ω => ∏ j, zpowSign (ζ j) (a ω (t j) (n j))) (μ.restrict F) := by
  by_cases hr : r = 0
  · subst r
    simpa only [Fin.prod_univ_zero] using (integrable_const (1 : ℂ) (μ := μ.restrict F))
  have hr1 : 1 ≤ r := by omega
  let m := fun ω => ∑' k, φ (latticePoint L k) * ‖g k ω‖ ^ 2
  have hm : MemLp m (r : ℝ≥0∞) μ := memLp_gaussian_mass g hg _ (fun k => hφ _)
    (MainGlue.summable_schwartz_lattice φ hL) r hr1
  have hm1 : MemLp (fun ω => 1 + m ω) (r : ℝ≥0∞) μ := (memLp_const (1 : ℝ)).add hm
  have henv : Integrable (fun ω => (1 + m ω) ^ r) (μ.restrict F) := by
    have h := hm1.integrable_norm_pow'
    have he (ω : Ω) : ‖1 + m ω‖ = 1 + m ω := Real.norm_of_nonneg
      (add_nonneg zero_le_one (tsum_nonneg fun k => mul_nonneg (hφ _) (sq_nonneg _)))
    simpa only [he] using h.restrict
  have hmeas' : Measurable fun ω => ∏ j, zpowSign (ζ j) (a ω (t j) (n j)) := by
    apply Finset.measurable_fun_prod
    intro j _
    have hj := hmeas _ (t j).2 (n j)
    unfold zpowSign
    split_ifs
    · exact hj
    · exact Complex.continuous_conj.measurable.comp hj
  apply henv.mono' hmeas'.aestronglyMeasurable.restrict
  apply ae_restrict_of_forall_mem hF
  intro ω hω
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin r, (1 + m ω) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => by
      have he : ‖zpowSign (ζ j) (a ω (t j) (n j))‖ = ‖a ω (t j) (n j)‖ := by
        unfold zpowSign
        split_ifs <;> simp
      rw [he]
      exact solution_norm_le_one_add_gaussian_mass hL φ hφ g ω (ha ω hω) (t j).2 (n j))
    _ = _ := by simp

end WaveTurbulence.Induct
