/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenBridge5
public import WaveTurbulence.Foundations.Spine.GenSplit
public import WaveTurbulence.Foundations.Spine.GroupVol
import Mathlib.Tactic
/-! Pattern decomposition of the time domain along paired rungs, and the Fourier family as a sum
over patterns. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Type} [Fintype Q] [DecidableEq Q] {K : Q → ℕ}

/-- Indexing of the paired rungs. -/
abbrev Jr (K : Q → ℕ) := Σ q, Fin (K q)

def xθ (ua va : Jr K → ι) (θ : Jr K → Bool) (j : Jr K) : ι := if θ j then ua j else va j
def yθ (ua va : Jr K → ι) (θ : Jr K → Bool) (j : Jr K) : ι := if θ j then va j else ua j

def ltθ (ch : ι → ι → Prop) (ua va : Jr K → ι) (θ : Jr K → Bool) (a b : ι) : Prop :=
  ch a b ∨ ∃ j, θ j = false ∧ a = ua j ∧ b = va j

def leθ (ua va : Jr K → ι) (θ : Jr K → Bool) (a b : ι) : Prop :=
  ∃ j, θ j = true ∧ a = va j ∧ b = ua j

/-- The valley region in the `X`-coordinates, for an identification `σ : Fin k ≃ Jr K`. -/
def RvOf {k : ℕ} (σ : Fin k ≃ Jr K) (D : ℝ) : Set (Fin k → ℝ) :=
  {tx | ∀ q, (fun j : Fin (K q) => tx (σ.symm ⟨q, j⟩)) ∈ Vset (K q) D}

/-- The pattern of a time vector. -/
noncomputable def patOf (ua va : Jr K → ι) (t : ι → ℝ) (j : Jr K) : Bool := decide (t (va j) ≤ t (ua j))

omit [DecidableEq ι] in
theorem Phi_eq_sum {Θ : Type} [Fintype Θ] (Ω : Set (ι → ℝ)) (Ωs : Θ → Set (ι → ℝ))
    (hΩs : ∀ θ, MeasurableSet (Ωs θ)) (T : ℝ) (hbs : ∀ θ, ∀ t ∈ Ωs θ, ∀ v, |t v| ≤ T)
    (hpart : ∀ t, (t ∈ Ω → ∃! θ, t ∈ Ωs θ) ∧ ∀ θ, t ∈ Ωs θ → t ∈ Ω)
    (L : ι → ℝ) (A : Finset ι) (α : ι → ℝ) :
    Phi Ω L A α = ∑ θ, Phi (Ωs θ) L A α := by
  unfold Phi
  rw [← integral_finsetSum _ (fun θ _ => integrable_indicator_famInt (Ωs θ) (hΩs θ) T (hbs θ) L A α)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show Ω.indicator (famInt L A α) t = ∑ θ, (Ωs θ).indicator (famInt L A α) t
  by_cases ht : t ∈ Ω
  · obtain ⟨θ0, h0, hu⟩ := (hpart t).1 ht
    rw [Set.indicator_of_mem ht, Finset.sum_eq_single θ0]
    · rw [Set.indicator_of_mem h0]
    · intro θ _ hθ
      have : t ∉ Ωs θ := fun h => hθ (hu θ h)
      rw [Set.indicator_of_notMem this]
    · intro h; exact absurd (Finset.mem_univ θ0) h
  · rw [Set.indicator_of_notMem ht]
    symm
    refine Finset.sum_eq_zero (fun θ _ => ?_)
    have : t ∉ Ωs θ := fun h => ht ((hpart t).2 θ h)
    rw [Set.indicator_of_notMem this]

end WaveTurbulence.Ladder
