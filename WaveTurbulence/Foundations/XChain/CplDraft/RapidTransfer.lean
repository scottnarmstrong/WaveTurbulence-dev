/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.BaseEvent
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# CPL-1, step 0: the rapid-decay good events

**Statement.** If `AnsatzAt P μ g a Fev R E Et q` holds, then it holds with each `Fev q` replaced by
`Fev q ∩ initialRapidEvent` (`ansatzAt_rapidFev`). The new events have the same restricted measures
(`restrict_rapidFev`), and on them the data have rapid decay. INDUCT's input lemmas take this as `hrapid`.

The rapid-decay event has probability one for Gaussian data (INDUCT `BaseEvent`), so no integral changes.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open MeasureTheory ProbabilityTheory Set Filter Induct

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]

/-- `Fev q ∩ {the data have rapid decay}`. -/
def rapidFev (g : (Fin P.d → ℤ) → Ω → ℂ) (Fev : ℕ → Set Ω) (q : ℕ) : Set Ω :=
  Fev q ∩ initialRapidEvent P.L P.φin g

omit [MeasurableSpace Ω] in
/-- The intersection of two symmetric events is symmetric. -/
theorem isSymmetricEvent_inter {d : ℕ} {L : ℝ} {φ : Mom d → ℝ} {g : (Fin d → ℤ) → Ω → ℂ}
    {F₁ F₂ : Set Ω} (h₁ : IsSymmetricEvent L φ g F₁) (h₂ : IsSymmetricEvent L φ g F₂) :
    IsSymmetricEvent L φ g (F₁ ∩ F₂) := by
  obtain ⟨A₁, hA₁, rfl, hg₁, ht₁⟩ := h₁
  obtain ⟨A₂, hA₂, rfl, hg₂, ht₂⟩ := h₂
  exact ⟨A₁ ∩ A₂, hA₁.inter hA₂, rfl, fun θ c hc => ⟨hg₁ θ c hc.1, hg₂ θ c hc.2⟩,
    fun x c hc => ⟨ht₁ x c hc.1, ht₂ x c hc.2⟩⟩

variable {P} (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin P.d → ℤ) → Ω → ℂ)

theorem rapidFev_ae_eq (hG : IsGaussianData μ g) (hL : 0 < P.L) (Fev : ℕ → Set Ω) (q : ℕ) :
    rapidFev P g Fev q =ᵐ[μ] Fev q := by
  have hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ := fun n => ⟨(hG.1 n).aemeasurable, hG.2.2 n⟩
  have he : initialRapidEvent P.L P.φin g =ᵐ[μ] (univ : Set Ω) :=
    eventuallyEqSet_univ.mpr (initialRapidEvent_ae hL P.φin g hlaw)
  have h := EventuallyEqSet.inter (by rfl : Fev q =ᵐ[μ] Fev q) he
  rwa [inter_univ] at h

theorem restrict_rapidFev (hG : IsGaussianData μ g) (hL : 0 < P.L) (Fev : ℕ → Set Ω) (q : ℕ) :
    μ.restrict (rapidFev P g Fev q) = μ.restrict (Fev q) :=
  Measure.restrict_congr_set (rapidFev_ae_eq μ g hG hL Fev q)

/-- **The ansatz on the rapid-decay events.** -/
theorem ansatzAt_rapidFev (hG : IsGaussianData μ g) (hL : 0 < P.L)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (q : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et q) : AnsatzAt P μ g a (rapidFev P g Fev) R E Et q := by
  have hres := restrict_rapidFev μ g hG hL Fev q
  have hreal : μ.real (rapidFev P g Fev q) = μ.real (Fev q) :=
    measureReal_congr (rapidFev_ae_eq μ g hG hL Fev q)
  obtain ⟨⟨hm, hs, hsub, hpr, hsol, hmeas, hint⟩, h2, h2', h3, h4⟩ := ha
  refine ⟨⟨hm.inter (measurableSet_initialRapidEvent P.L P.φin hG.1),
    isSymmetricEvent_inter hs (symmetric_initialRapidEvent P.L P.φin g),
    fun h1 => inter_subset_inter_left _ (hsub h1), hreal ▸ hpr, fun ω hω => hsol ω hω.1, hmeas,
    fun r t n ζ => hres ▸ hint r t n ζ⟩, ?_, ?_, ?_, ?_⟩
  · rw [hres]; exact h2
  · rw [hres]; exact h2'
  · rw [hres]; exact h3
  · exact h4

omit [MeasurableSpace Ω] in
theorem rapid_of_mem_rapidFev (Fev : ℕ → Set Ω) (q : ℕ) :
    ∀ ω ∈ rapidFev P g Fev q, IsRapidDecay (initialCoeff P.L P.φin g ω) :=
  fun _ hω => hω.2

end WaveTurbulence.Cpl
