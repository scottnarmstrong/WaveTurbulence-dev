/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.NLS.Backward
public import WaveTurbulence.Foundations.MainGlue.SchwartzMass
/-! SEAL-PLAN B.4: exact consumption of snapshot-4 AnsatzAt item (1). -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory Set

variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : (Fin P.d → ℤ) → Ω → ℂ} {a : Ω → ℝ → (Fin P.d → ℤ) → ℂ}
  {Fev : ℕ → Set Ω} {R : ℕ → Mom P.d → ℝ} {E : ℕ → (Fin P.d → ℤ) → ℝ}
  {Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ}
  {p : ℕ}

/-- TARGET propansatz (1): consume the actual draft ansatz, not an assumed solution proxy. -/
theorem ansatz_isAkSolution (hA : AnsatzAt P μ g a Fev R E Et p)
    {ω : Ω} (hω : ω ∈ Fev p) :
    NLS.IsAkSolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) :=
  (hA.1.2.2.2.2.1 ω hω).1

/-- TARGET propansatz (1): the one-step event nesting has the stated positive-level guard. -/
theorem ansatz_event_subset_predecessor (hA : AnsatzAt P μ g a Fev R E Et p)
    (hp : 1 ≤ p) : Fev p ⊆ Fev (p - 1) := hA.1.2.2.1 hp

end WaveTurbulence.MainGlue
