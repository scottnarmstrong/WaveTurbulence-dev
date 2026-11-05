/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PrefixNextData
public import WaveTurbulence.Foundations.XChain.PrefixVarianceBound
public import WaveTurbulence.Foundations.XChain.KernelMomentumSupport
public import WaveTurbulence.Foundations.XChain.AnsatzHistory
/-! All literal clauses of AnsatzAt hold at the newly constructed prefix endpoint. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set Finset
universe u

theorem prefix_next_ansatz {P : WTParams} (H : InductContext.{u} P)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    {p : ℕ} (hp : p < P.D) (S : AnsatzPrefixData P μ g p) (T : PrefixExtension S) :
    AnsatzAt P μ g T.a T.nextFev T.nextR T.nextE T.nextEt (p + 1) := by
  have hend : (p : ℝ) + 1 ∈ Ioc (p : ℝ) (p + 1) := ⟨by linarith, le_rfl⟩
  have hglobal : (p : ℝ) + 1 ∈ Icc (0 : ℝ) (p + 1) := ⟨by positivity, le_rfl⟩
  have hrapid : ∀ ω ∈ T.F, IsRapidDecay (initialCoeff P.L P.φin g ω) :=
    fun ω hω => S.rapid_at ω (T.subset hω)
  simp only [AnsatzAt, T.nextFev_new, T.nextR_new, PrefixExtension.nextE, PrefixExtension.nextEt,
    Function.update_self, Nat.cast_add, Nat.cast_one]
  refine ⟨⟨T.measurable, T.symmetric, ?_, T.probability, ?_, T.measurable_a, ?_⟩,
    ⟨prefix_next_remainder_bound H μ g hp S _ hend, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro _
    simpa only [Nat.add_sub_cancel_right, T.nextFev_old le_rfl] using T.subset
  · exact fun ω hω => ⟨T.solution ω hω, T.unique_solution ω hω⟩
  · intro r t n sig
    let times : Fin r → Icc (0 : ℝ) ((p : ℝ) + 1) := fun j =>
      ⟨(t j).1, by simpa only [Nat.cast_add, Nat.cast_one] using (t j).2⟩
    exact T.products r times n sig
  · intro n
    simpa only [T.nextR_new, Nat.cast_add, Nat.cast_one] using
      prefix_next_variance_error H μ g hG hp S T n _ hend
  · intro n n'
    by_cases hn : n = n'
    · subst n'
      rw [ite_eq_left rfl]
      have he : (fun ω => T.a ω (p + 1) n * (starRingEnd ℂ) (T.a ω (p + 1) n)) =
          fun ω => ((‖T.a ω (p + 1) n‖ ^ 2 : ℝ) : ℂ) := by
        funext ω
        simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [he, integral_complex_ofReal]
      push_cast
      ring
    · rw [ite_eq_right hn]
      exact solution_covariance_off_diagonal (zero_lt_one.trans_le H.L_ge_one) P.φin hG
        T.F T.measurable T.symmetric T.a T.solution hrapid T.measurable_a _ hglobal n n' hn
  · intro _ t ht n
    apply prefix_next_variance_bound H μ g hG hp S T n t
    constructor <;> linarith [ht.1, ht.2]
  · intro m hm hmR sig hbal n
    have hk : (∑ N ∈ range (P.N (p + 1) + 1), truncSum P (inputsF P T.nextR) (p + 1) N (p + 1) sig n) =
        ∑ N ∈ range (P.N (p + 1) + 1), truncSum P (inputsF P S.R) (p + 1) N (p + 1) sig n :=
      sum_congr rfl fun N _ => T.next_truncSum le_rfl N _ sig n
    rw [hk]
    refine ⟨by unfold jointCumulant cumulant; ring, ?_, prefix_next_higher_error H μ g hG hp S T m hm hmR sig hbal n _ hend⟩
    intro hn
    have hz := cumulant_signed_solution_eq_zero_of_momentum (zero_lt_one.trans_le H.L_ge_one)
      P.φin hG T.F T.measurable T.symmetric T.a T.solution hrapid T.measurable_a
      (fun _ : Fin (2 * m) => ⟨(p : ℝ) + 1, hglobal⟩) n sig univ hn
    have hsum : (∑ N ∈ range (P.N (p + 1) + 1), truncSum P (inputsF P S.R) (p + 1) N (p + 1) sig n) = 0 :=
      sum_eq_zero fun N _ => truncSum_eq_zero_of_momentum P (inputsF P S.R) (p + 1) N _ sig n hn
    change cumulant (μ.restrict T.F) (fun j ω => zpowSign (sig j) (T.a ω (p + 1) (n j))) univ - _ = 0
    rw [hz, hsum, sub_zero]
  · intro m hm hmR sig hbal n N hN
    rw [T.next_truncSum le_rfl]
    exact layergarden_next_order_bound P H.layergarden S.R p hp S.remainderBound
      H.L_ge_one H.delta_pos H.delta_le_one H.nu_nonneg (by have h := (H.sizes.2.2.2 p hp).1; omega)
      m hm hmR sig hbal n N hN _ hend

end WaveTurbulence.Induct
