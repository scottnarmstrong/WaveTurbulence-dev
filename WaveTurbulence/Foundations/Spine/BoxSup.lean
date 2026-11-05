/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.PhiFamily
import Mathlib.Tactic
/-! The elementary inequality for the Fourier transform `B(α) = Φ_∅(α)` of a time domain:
`sup_{α ∈ a + [0,1]^ι} |B| ≤ ∑_A ∫_{a+[0,1]^ι} |Φ_A|` (TARGET L2004–L2008). -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem boxμ_pi_eq : Measure.pi (boxμ ι) = (volume : Measure (ι → ℝ)).restrict (Set.pi univ (fun _ => Icc (0:ℝ) 1)) := by
  rw [volume_pi, ← Measure.restrict_pi_pi]

theorem elem_sup_Phi (Ω : Set (ι → ℝ)) (hΩm : MeasurableSet Ω) (T : ℝ)
    (hΩb : ∀ t ∈ Ω, ∀ v, |t v| ≤ T) (L : ι → ℝ) (a x : ι → ℝ)
    (hx : ∀ v, x v ∈ Icc (a v) (a v + 1)) :
    ‖Phi Ω L ∅ x‖ₑ ≤ ∑ A : Finset ι,
      ∫⁻ y in Set.pi univ (fun v => Icc (a v) (a v + 1)), ‖Phi Ω L A y‖ₑ := by
  set Φ : Finset ι → (ι → ℝ) → ℂ := fun A y => Phi Ω L A (a + y) with hΦ
  have hc : ∀ A, Continuous (Φ A) := fun A =>
    (continuous_Phi Ω hΩm T hΩb L A).comp (continuous_const.add continuous_id)
  have hd : ∀ A b, b ∉ A → ∀ y : ι → ℝ,
      HasDerivAt (fun r => Φ A (update y b r))
        (Φ (insert b A) y + ((Real.pi * L b : ℝ) : ℂ) * Complex.I * Φ A y) (y b) := by
    intro A b hb y
    have h := hasDerivAt_Phi Ω hΩm T hΩb L A b hb (a + y)
    have h3 := HasDerivAt.comp_const_add (a b) (y b) (f := fun s => Phi Ω L A (update (a + y) b s)) h
    have hfun : (fun r : ℝ => Φ A (update y b r)) =
        fun r : ℝ => Phi Ω L A (update (a + y) b (a b + r)) := by
      funext r; simp only [hΦ]; congr 1; funext v
      by_cases hv : v = b
      · subst hv; simp
      · simp [update_of_ne hv]
    rw [hfun]
    have hΦy : Φ (insert b A) y + ((Real.pi * L b : ℝ) : ℂ) * Complex.I * Φ A y =
        Phi Ω L (insert b A) (a + y) + ((Real.pi * L b : ℝ) : ℂ) * Complex.I * Phi Ω L A (a + y) := rfl
    rw [hΦy]
    exact h3
  have hx' : ∀ v, (x - a) v ∈ Icc (0:ℝ) 1 := fun v => by
    have := hx v; simp only [Pi.sub_apply, Set.mem_Icc] at this ⊢; constructor <;> linarith [this.1, this.2]
  have h := elementary_sup_le Φ (fun b => Real.pi * L b) hc hd (x - a) hx'
  have e0 : Φ ∅ (x - a) = Phi Ω L ∅ x := by simp [hΦ]
  rw [e0] at h
  refine h.trans (Finset.sum_le_sum (fun A _ => le_of_eq ?_))
  rw [lmarginal_univ, boxμ_pi_eq]
  simp only [hΦ]
  set S : Set (ι → ℝ) := Set.pi univ (fun _ => Icc (0:ℝ) 1) with hS
  set S' : Set (ι → ℝ) := Set.pi univ (fun v => Icc (a v) (a v + 1)) with hS'
  have hSm : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hS'm : MeasurableSet S' := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hmem : ∀ x, (a + x ∈ S') ↔ x ∈ S := by
    intro x
    simp only [hS, hS', Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Pi.add_apply]
    refine forall_congr' (fun v => ?_)
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← lintegral_indicator hSm, ← lintegral_indicator hS'm,
    ← lintegral_add_left_eq_self (fun y => S'.indicator (fun z => ‖Phi Ω L A z‖ₑ) y) a]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ S
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx)]
  · have : a + x ∉ S' := fun h => hx ((hmem x).mp h)
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]

end WaveTurbulence.Ladder
