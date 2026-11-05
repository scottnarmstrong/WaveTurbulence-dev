/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzBase
public import WaveTurbulence.Foundations.XChain.InitialL1Moments
/-! Internal finite-prefix induction data; l1 moments and future-zero remainders are proved invariants. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal

structure AnsatzPrefixData (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ) (p : ℕ) where
  a : Ω → ℝ → (Fin P.d → ℤ) → ℂ
  Fev : ℕ → Set Ω
  R : ℕ → Mom P.d → ℝ
  E : ℕ → (Fin P.d → ℤ) → ℝ
  Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ
  ansatz : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q
  rapid : ∀ ω ∈ Fev 0, IsRapidDecay (initialCoeff P.L P.φin g ω)
  future_zero : ∀ q, p < q → R q = 0
  l1_moments : ∀ q ≤ p, ∀ r : ℕ, 1 ≤ r →
    MemLp (fun ω => ∑' n, ‖a ω q n‖) (r : ℝ≥0∞) (μ.restrict (Fev q))

noncomputable def basePrefixData (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin P.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g) (hL : 0 < P.L) (hδ : 0 ≤ P.δ)
    (hφ : ∀ k, 0 ≤ P.φin k) (hinit : P.φ 0 = P.φin) : AnsatzPrefixData P μ g 0 where
  a := fun ω _ => initialCoeff P.L P.φin g ω
  Fev := fun _ => initialRapidEvent P.L P.φin g
  R := fun _ _ => 0
  E := fun _ _ => 0
  Et := fun _ _ _ _ => 0
  ansatz := by
    intro q hq
    have he : q = 0 := by omega
    subst q
    exact ansatz_zero P μ g hG hL hδ hφ hinit
  rapid := fun _ hω => hω
  future_zero := fun _ _ => rfl
  l1_moments := by
    intro q _ r hr
    exact (memLp_initial_l1 hL P.φin g
      (fun n => ⟨(hG.1 n).aemeasurable, hG.2.2 n⟩) r hr).mono_measure Measure.restrict_le_self

end WaveTurbulence.Induct
