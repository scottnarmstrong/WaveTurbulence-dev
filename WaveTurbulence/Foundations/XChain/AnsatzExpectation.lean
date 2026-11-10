/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MainAsmGateTypes
public import WaveTurbulence.Foundations.XChain.AnsatzMass
public import WaveTurbulence.Foundations.XChain.AnsatzIdentification
public import WaveTurbulence.Foundations.XChain.ExpectationComparison
/-! Conditional event and expectation assembly from the exact Wave B gates, SEAL-PLAN B.2–B.4. -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u
variable {P : WTParams} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ}
  {Fev : ℕ → Set Ω} {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}

/-- G1/G2 consumed from the actual universally quantified bridge gate. -/
theorem gate_solvable_measurability (hB : NlsAkBridgeGate.{u}) (hd : 1 ≤ P.d)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hD : 1 ≤ P.D) {α T : ℝ}
    (hα : α = P.L ^ (-P.γ)) (hT : T = P.δ * kineticTime α * P.D)
    (hg : ∀ n, Measurable (g n)) :
    MeasurableSet (solvableEvent P.L α T P.φin g) ∧
    ∀ U : Ω → ℝ → (Fin P.d → ℝ) → ℂ,
      (∀ ω ∈ solvableEvent P.L α T P.φin g,
        IsSmoothNLSSolution P.L α T (initialCoeff P.L P.φin g ω) (U ω)) →
      ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
        (solvableEvent P.L α T P.φin g).indicator
          (fun ω => ‖torusFourierCoeff P.L (U ω t) n‖ ^ 2) ω := by
  have hb := hB hd P.L P.γ P.δ hL hδ P.D hD α T hα (by rw [hT]; ring)
  exact hb.2.2.2 Ω (initialCoeff P.L P.φin g) (NLS.measurable_initialCoeff P.L P.φin hg)

/-- The final ansatz probability passes through rapid decay almost surely and G4. -/
theorem ansatz_solvable_probability (hA : AnsatzAt P μ g a Fev R E Et P.D)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hD : 1 ≤ P.D) {α T : ℝ}
    (hα : α = P.L ^ (-P.γ)) (hT : T = P.δ * kineticTime α * P.D)
    (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    1 - Real.exp (-(P.N P.D : ℝ)) ≤ μ.real (solvableEvent P.L α T P.φin g) := by
  have hr := Probability.ae_initialCoeff_isRapidDecay hL P.φin g hg
  have he : Fev P.D =ᵐ[μ] Fev P.D ∩ {ω | IsRapidDecay (initialCoeff P.L P.φin g ω)} := by
    filter_upwards [hr] with ω hω
    exact propext ⟨fun h => ⟨h, hω⟩, fun h => h.1⟩
  calc
    _ ≤ μ.real (Fev P.D) := hA.1.2.2.2.1
    _ = μ.real (Fev P.D ∩ {ω | IsRapidDecay (initialCoeff P.L P.φin g ω)}) := measureReal_congr he
    _ ≤ _ := measureReal_mono (ansatz_event_inter_rapid_subset_solvable hL hδ hD hα hT hA)

/-- The full expectation estimate before the elementary large-L absorption.
Both observables are proved integrable; the comparison uses Fev D, not Fev p⊆solvableEvent. -/
theorem ansatz_observable_error (hB : NlsAkBridgeGate.{u}) (hd : 1 ≤ P.d)
    (hA : ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hD : 1 ≤ P.D)
    (hφ : ∀ k, 0 ≤ P.φin k) {α T : ℝ} (hα : α = P.L ^ (-P.γ))
    (hT : T = P.δ * kineticTime α * P.D)
    (hg : ∀ n, Measurable (g n)) (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ)
    (U : Ω → ℝ → (Fin P.d → ℝ) → ℂ)
    (hU : ∀ ω ∈ solvableEvent P.L α T P.φin g,
      IsSmoothNLSSolution P.L α T (initialCoeff P.L P.φin g ω) (U ω))
    {t : ℝ} (ht : t ∈ Icc 0 T) {p : ℕ} (hp1 : 1 ≤ p) (hpD : p ≤ P.D)
    (hs : t / (P.δ * kineticTime α) ∈ Icc ((p : ℝ) - 1) p) (n : Fin P.d → ℤ) :
    |(∫ ω, (solvableEvent P.L α T P.φin g).indicator
        (fun ω => ‖torusFourierCoeff P.L (U ω t) n‖ ^ 2) ω ∂μ) -
      P.φ (P.δ * (t / (P.δ * kineticTime α))) (latticePoint P.L n)| ≤
      2 * P.L ^ (-P.theta p) + 2 * Real.sqrt 2 *
        (∑' m, P.φin (latticePoint P.L m)) * Real.exp (-(P.N P.D : ℝ) / 2) := by
  let F := solvableEvent P.L α T P.φin g
  let s := t / (P.δ * kineticTime α)
  let f := F.indicator (fun ω => ‖torusFourierCoeff P.L (U ω t) n‖ ^ 2)
  let v := (Fev p).indicator (fun ω => ‖a ω s n‖ ^ 2)
  let M := fun ω => ∑' m, P.φin (latticePoint P.L m) * ‖g m ω‖ ^ 2
  have hAp := hA p hpD
  have hAD := hA P.D le_rfl
  have hs0p : s ∈ Icc (0 : ℝ) p :=
    ⟨(sub_nonneg.mpr (show (1 : ℝ) ≤ p by exact_mod_cast hp1)).trans hs.1, hs.2⟩
  have hMi : Integrable M μ := integrable_initial_mass hL P.φin hφ g hlaw
  have hM0 (ω : Ω) : 0 ≤ M ω := tsum_nonneg (fun _ => mul_nonneg (hφ _) (sq_nonneg _))
  have hf0 (ω : Ω) : 0 ≤ f ω := indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hv0 (ω : Ω) : 0 ≤ v ω := indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hfM (ω : Ω) : f ω ≤ M ω := by
    by_cases hω : ω ∈ F
    · dsimp only [f]
      rw [indicator_of_mem hω]
      exact NLS.norm_torusFourierCoeff_sq_le_tsum hL hφ (hU ω hω) ht n
    · dsimp only [f]
      rw [indicator_of_notMem hω]
      exact hM0 ω
  have hvM (ω : Ω) : v ω ≤ M ω := by
    by_cases hω : ω ∈ Fev p
    · dsimp only [v]
      rw [indicator_of_mem hω]
      exact ansatz_norm_sq_le_initial_mass hAp hL hφ hω hs0p n
    · dsimp only [v]
      rw [indicator_of_notMem hω]
      exact hM0 ω
  have hmeas := gate_solvable_measurability hB hd hL hδ hD hα hT hg
  have hfm : Measurable f := hmeas.2 U hU t ht n
  have hvm : Measurable v :=
    ((hAp.1.2.2.2.2.2.1 s hs0p n).norm.pow_const 2).indicator hAp.1.1
  have hfi : Integrable f μ := hMi.mono' hfm.aestronglyMeasurable
    (ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (hf0 ω)]; exact hfM ω))
  have hvi : Integrable v μ := hMi.mono' hvm.aestronglyMeasurable
    (ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (hv0 ω)]; exact hvM ω))
  have he : ∀ᵐ ω ∂μ, ω ∈ Fev P.D → f ω = v ω := by
    filter_upwards [Probability.ae_initialCoeff_isRapidDecay hL P.φin g hlaw] with ω hr
    intro hω
    have hωF := ansatz_event_inter_rapid_subset_solvable hL hδ hD hα hT hAD ⟨hω, hr⟩
    have hωp := ansatz_event_subset hA hpD hω
    dsimp only [f, v]
    rw [indicator_of_mem hωF, indicator_of_mem hωp]
    rw [ansatz_selection_norm_torusFourierCoeff_eq hAD hL hδ hD hα hT U hU ⟨hω, hr⟩ ht n]
  have hdiff := integral_sub_le_mass_compl hfi hvi hMi hAD.1.1
    (fun ω => ⟨hf0 ω, hfM ω, hv0 ω, hvM ω⟩) he
  have hcomp : μ.real (Fev P.D)ᶜ ≤ Real.exp (-(P.N P.D : ℝ)) := by
    rw [measureReal_compl hAD.1.1, probReal_univ]
    linarith only [hAD.1.2.2.2.1]
  have hmass := integral_initial_mass_restrict_le hL P.φin hφ g hlaw (Fev P.D)ᶜ
  have hsum0 : 0 ≤ ∑' m, P.φin (latticePoint P.L m) := tsum_nonneg (fun _ => hφ _)
  have htail : (∫ ω in (Fev P.D)ᶜ, M ω ∂μ) ≤
      2 * Real.sqrt 2 * (∑' m, P.φin (latticePoint P.L m)) * Real.exp (-(P.N P.D : ℝ) / 2) := by
    calc
      _ ≤ Real.sqrt 2 * Real.sqrt (μ.real (Fev P.D)ᶜ) * ∑' m, P.φin (latticePoint P.L m) := hmass
      _ ≤ Real.sqrt 2 * Real.sqrt (Real.exp (-(P.N P.D : ℝ))) * ∑' m, P.φin (latticePoint P.L m) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcomp)
          (Real.sqrt_nonneg _)) hsum0
      _ = Real.sqrt 2 * (∑' m, P.φin (latticePoint P.L m)) * Real.exp (-(P.N P.D : ℝ) / 2) := by
        rw [← Real.exp_half]
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using le_mul_of_one_le_left
          (show 0 ≤ Real.sqrt 2 * (∑' m, P.φin (latticePoint P.L m)) * Real.exp (-(P.N P.D : ℝ) / 2) from
            mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hsum0) (Real.exp_nonneg _))
          (by norm_num : (1 : ℝ) ≤ 2)
  have hstep : |(∫ ω, v ω ∂μ) - P.φ (P.δ * s) (latticePoint P.L n)| ≤ 2 * P.L ^ (-P.theta p) := by
    simpa only [v, integral_indicator hAp.1.1] using hAp.2.2.1 hp1 s hs n
  exact (abs_sub_le (∫ ω, f ω ∂μ) (∫ ω, v ω ∂μ) _).trans
    ((add_le_add (hdiff.trans htail) hstep).trans_eq (add_comm _ _))

end WaveTurbulence.MainGlue
