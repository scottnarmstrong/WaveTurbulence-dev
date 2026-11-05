/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BaseGaussian
public import WaveTurbulence.Foundations.XChain.BaseEvent
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! T.ansatzBase, TARGET L708–709, with the approved full-measure rapid-decay base event. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- No canonical gardens occur at level zero. -/
theorem truncSum_zero_level (P : WTParams) (F : ℕ → Mom P.d → ℝ) (N : ℕ) {w : ℕ}
    (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P F 0 N t ζ n = 0 := by
  simp [truncSum, IsCanonGC]

theorem iterPartial_zero_function {d : ℕ} (ρ : Fin d → ℕ) :
    iterPartial ρ (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
  have hp (j : Fin d) : partialMom j (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
    funext k
    simp [partialMom]
  have hi (j : Fin d) (N : ℕ) : (partialMom j)^[N] (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
    induction N with
    | zero => rfl
    | succ N ih => rw [Function.iterate_succ_apply', ih, hp]
  unfold iterPartial
  generalize List.finRange d = l
  induction l with
  | nil => rfl
  | cons j l ih => simpa only [List.foldr_cons, ih] using hi j (ρ j)

theorem SNormR_zero_function {d : ℕ} (Λ₁ Λ₂ : ℕ) :
    SNormR Λ₁ Λ₂ (fun _ : Mom d => 0) = 0 := by
  simp only [SNormR, Complex.ofReal_zero, SNorm, ite_eq_left (Or.inr contDiff_const),
    iterPartial_zero_function, norm_zero, mul_zero, ENNReal.ofReal_zero]
  exact le_antisymm (iSup_le (fun _ => iSup_le (fun _ => iSup_le (fun _ => le_rfl)))) zero_le

/-- The full literal AnsatzAt at p=0, not merely its Gaussian-moment conjuncts.
Fev₀ differs from the source's Ω only by a null set, as explicitly approved by the author. -/
theorem ansatz_zero (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin P.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g) (hL : 0 < P.L) (hδ : 0 ≤ P.δ)
    (hφ : ∀ k, 0 ≤ P.φin k) (hinit : P.φ 0 = P.φin) :
    AnsatzAt P μ g (fun ω _ => initialCoeff P.L P.φin g ω)
      (fun _ => initialRapidEvent P.L P.φin g) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ _ _ => 0) 0 := by
  classical
  have hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ :=
    fun n => MainGlue.hasLaw_stdComplexGaussian (hG.1 n) (hG.2.2 n)
  have hrestr := restrict_initialRapidEvent hL P.φin g hlaw
  simp only [AnsatzAt, Nat.cast_zero, mul_zero, hinit, add_zero]
  refine ⟨⟨measurableSet_initialRapidEvent P.L P.φin hG.1,
    symmetric_initialRapidEvent P.L P.φin g, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro hp
    omega
  · rw [measure_initialRapidEvent hL P.φin g hlaw]
    exact sub_le_self _ (Real.exp_nonneg _)
  · intro ω hω
    refine ⟨isASolution_zero_of_rapidDecay (γ := P.γ) (δ := P.δ) hL hω, ?_⟩
    intro b hb t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact hb.1
  · intro t ht n
    exact (hG.1 n).const_mul _
  · intro r t n ζ
    rw [hrestr]
    exact initial_signed_prod_integrable hG.2.1 hlaw P.L P.φin n ζ
  · refine ⟨?_, ?_, ?_⟩
    · rw [SNormR_zero_function]
      exact zero_le
    · intro n
      simp only [abs_zero]
      exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_nonneg _)
    · intro n n'
      rw [hrestr, initial_covariance hG.2.1 hlaw P.L P.φin hφ]
  · intro hp
    omega
  · intro m hm _ ζ _ n
    rw [hrestr, initial_higher_cumulant_zero hG.2.1 hlaw (by omega : 3 ≤ 2 * m)]
    simp only [truncSum_zero_level, Finset.sum_const_zero, norm_zero, implies_true, true_and]
    exact mul_nonneg (Real.rpow_nonneg (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)) _)
      (Real.exp_nonneg _)
  · intro m _ _ ζ _ n N _
    rw [truncSum_zero_level, norm_zero]
    exact mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)) _)
      (Real.rpow_nonneg hL.le _)) (Real.rpow_nonneg hδ _)

end WaveTurbulence.Induct
