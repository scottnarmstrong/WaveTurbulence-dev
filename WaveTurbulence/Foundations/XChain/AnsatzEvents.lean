/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInterface
/-! G4 and G11, SEAL-PLAN B.4; TARGET propansatz (1) and the proof of Theorem 1.1. -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory Set
variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ}
  {Fev : ℕ → Set Ω} {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}

/-- G11: every later ansatz event lies in each earlier one, including level zero. -/
theorem ansatz_event_subset {q : ℕ}
    (hA : ∀ i ≤ q, AnsatzAt P μ g a Fev R E Et i) {p : ℕ} (hp : p ≤ q) :
    Fev q ⊆ Fev p := by
  induction q generalizing p with
  | zero =>
    have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
    subst p
    exact subset_rfl
  | succ q ih =>
    by_cases hpq : p = q + 1
    · subst p
      exact subset_rfl
    · have hp' : p ≤ q := by omega
      have hq : ∀ i ≤ q, AnsatzAt P μ g a Fev R E Et i :=
        fun i hi => hA i (hi.trans (Nat.le_succ q))
      have hs : Fev (q + 1) ⊆ Fev q := by
        simpa only [Nat.add_sub_cancel] using
          ansatz_event_subset_predecessor (hA (q + 1) le_rfl) (Nat.succ_pos q)
      exact hs.trans (ih hq hp')

/-- G4: positive final time and rapid initial decay turn the final classed solution into
an actual smooth NLS solution on the entire physical interval. -/
theorem ansatz_event_inter_rapid_subset_solvable (hL : 0 < P.L) (hδ : 0 < P.δ)
    (hD : 0 < P.D) {α T : ℝ} (hα : α = P.L ^ (-P.γ))
    (hT : T = P.δ * kineticTime α * P.D)
    (hA : AnsatzAt P μ g a Fev R E Et P.D) :
    Fev P.D ∩ {ω | IsRapidDecay (initialCoeff P.L P.φin g ω)} ⊆
      solvableEvent P.L α T P.φin g := by
  subst α
  intro ω hω
  have ha := ansatz_isAkSolution hA hω.1
  have hb := NLS.IsAkSolution.isSmoothNLSSolution hL hδ
    (show (0 : ℝ) < P.D by exact_mod_cast hD) hT hω.2 ha
  exact ⟨NLS.backSolution P.L P.γ P.δ (initialCoeff P.L P.φin g ω) (a ω), hb.1⟩

end WaveTurbulence.MainGlue
