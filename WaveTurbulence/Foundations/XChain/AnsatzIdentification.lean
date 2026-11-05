/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzEvents
/-! G9, SEAL-PLAN B.4: exact reduced-coefficient and physical Fourier-norm identification.
TARGET (reducedcoef), L545, and proof of Theorem 1.1, L818–820. -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory Set
variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ}
  {Fev : ℕ → Set Ω} {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}

/-- G9 before taking norms: the reduced coefficients equal the actual a-system by class uniqueness. -/
theorem ansatz_reducedCoeff_eq {p : ℕ} (hA : AnsatzAt P μ g a Fev R E Et p)
    (hL : 0 < P.L) (hδ : 0 ≤ P.δ) {T : ℝ}
    (hT : T = P.δ * kineticTime (P.L ^ (-P.γ)) * p)
    {ω : Ω} (hω : ω ∈ Fev p) {u : ℝ → (Fin P.d → ℝ) → ℂ}
    (hu : IsSmoothNLSSolution P.L (P.L ^ (-P.γ)) T (initialCoeff P.L P.φin g ω) u) :
    ∀ s ∈ Icc (0 : ℝ) p, NLS.reducedCoeff P.L P.γ P.δ u s = a ω s :=
  (hu.isAkSolution hL hδ hT).eq_of_eq hL (ansatz_isAkSolution hA hω)

/-- G9 at any level p: identify Fourier norms on the whole physical interval, including endpoints.
For an already supplied smooth solution no rapid-decay or positive-level premise is required. -/
theorem ansatz_norm_torusFourierCoeff_eq {p : ℕ} (hA : AnsatzAt P μ g a Fev R E Et p)
    (hL : 0 < P.L) (hδ : 0 < P.δ) {α T : ℝ} (hα : α = P.L ^ (-P.γ))
    (hT : T = P.δ * kineticTime α * p) {ω : Ω} (hω : ω ∈ Fev p)
    {u : ℝ → (Fin P.d → ℝ) → ℂ}
    (hu : IsSmoothNLSSolution P.L α T (initialCoeff P.L P.φin g ω) u)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin P.d → ℤ) :
    ‖torusFourierCoeff P.L (u t) n‖ = ‖a ω (t / (P.δ * kineticTime α)) n‖ := by
  subst α
  have hkt : 0 < kineticTime (P.L ^ (-P.γ)) := by
    rw [NLS.kineticTime_rpow_neg hL P.γ]
    exact div_pos (Real.rpow_pos_of_pos hL _) (by norm_num)
  have hσ : 0 < P.δ * kineticTime (P.L ^ (-P.γ)) := mul_pos hδ hkt
  have hs : t / (P.δ * kineticTime (P.L ^ (-P.γ))) ∈ Icc (0 : ℝ) p := by
    refine ⟨div_nonneg ht.1 hσ.le, (div_le_iff₀' hσ).mpr ?_⟩
    rw [← hT]
    exact ht.2
  have he := ansatz_reducedCoeff_eq hA hL hδ.le hT hω hu _ hs
  calc
    _ = ‖NLS.reducedCoeff P.L P.γ P.δ u (t / (P.δ * kineticTime (P.L ^ (-P.γ)))) n‖ := by
      rw [NLS.norm_reducedCoeff, mul_div_cancel₀ t hσ.ne']
    _ = _ := by rw [he]

/-- G9 in main's selection form: on the final ansatz event intersected with rapid data,
any smooth-solution selection on the frozen solvable event has the a-system Fourier norms. -/
theorem ansatz_selection_norm_torusFourierCoeff_eq
    (hA : AnsatzAt P μ g a Fev R E Et P.D) (hL : 0 < P.L) (hδ : 0 < P.δ)
    (hD : 0 < P.D) {α T : ℝ} (hα : α = P.L ^ (-P.γ))
    (hT : T = P.δ * kineticTime α * P.D)
    (U : Ω → ℝ → (Fin P.d → ℝ) → ℂ)
    (hU : ∀ ω ∈ solvableEvent P.L α T P.φin g,
      IsSmoothNLSSolution P.L α T (initialCoeff P.L P.φin g ω) (U ω))
    {ω : Ω} (hω : ω ∈ Fev P.D ∩ {ω | IsRapidDecay (initialCoeff P.L P.φin g ω)})
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin P.d → ℤ) :
    ‖torusFourierCoeff P.L (U ω t) n‖ = ‖a ω (t / (P.δ * kineticTime α)) n‖ := by
  have hsolv := ansatz_event_inter_rapid_subset_solvable hL hδ hD hα hT hA hω
  exact ansatz_norm_torusFourierCoeff_eq hA hL hδ hα hT hω.1 (hU ω hsolv) ht n

end WaveTurbulence.MainGlue
