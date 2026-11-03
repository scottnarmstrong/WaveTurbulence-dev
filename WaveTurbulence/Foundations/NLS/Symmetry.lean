/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.UniformDecay

/-!
# Gauge and space-translation symmetry of (NLS) and of the solvability event

TARGET (gaugeinv), L567–L570, uses gauge invariance `u ↦ e^{iθ}u` and space translation invariance
`u ↦ u(· - x₀)` of (NLS) and of the event that (NLS) has a smooth solution. With
`smoothDataSet L α T = {c : ∃ u, IsSmoothNLSSolution L α T c u}`:

* `IsSmoothNLSSolution.gauge`, `IsSmoothNLSSolution.translate`: the solution map commutes with the
  symmetries; on the data, `c ↦ e^{iθ} c` and `cₙ ↦ e^{-2πi⟨n/L, x₀⟩} cₙ`
  (`= torusChar L n (-x₀) * cₙ`);
* `mem_smoothDataSet_gauge_iff`, `mem_smoothDataSet_translate_iff`: `smoothDataSet` is invariant;
* `solvableEvent_eq_preimage`, `solvableEvent_gauge`, `solvableEvent_translate`: `solvableEvent` is
  the preimage of `smoothDataSet` under the data map, and is unchanged when the random coefficients
  `g` are rotated or modulated (the "gauge or space translation symmetry" of L569, in the form
  `IsSymmetricEvent` of the Wave B proposal §2.3.4);
* `reducedCoeff_gauge`, `reducedCoeff_translate`: the transformation laws of the reduced
  coefficients `a_k(t)` of (reducedcoef).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- The data `c` for which (NLS) has a smooth solution on `[0, T]`. -/
@[expose] def smoothDataSet (L α T : ℝ) : Set ((Fin d → ℤ) → ℂ) :=
  {c | ∃ u, IsSmoothNLSSolution L α T c u}

theorem solvableEvent_eq_preimage {Ω : Type*} (L α T : ℝ) (φin : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) :
    solvableEvent L α T φin g = (fun o => initialCoeff L φin g o) ⁻¹' smoothDataSet L α T :=
  rfl

/-! ### Calculus lemmas -/

theorem normLaplacian_const_mul (z : ℂ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    normLaplacian (fun y => z * f y) x = z * normLaplacian f x := by
  simp only [normLaplacian, partialDeriv, deriv_const_mul_field', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem update_sub (x x₀ : Fin d → ℝ) (j : Fin d) (r : ℝ) :
    Function.update x j r - x₀ = Function.update (x - x₀) j (r - x₀ j) := by
  ext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk]

theorem partialDeriv_comp_sub (j : Fin d) (f : (Fin d → ℝ) → ℂ) (x₀ : Fin d → ℝ) :
    partialDeriv j (fun y => f (y - x₀)) = fun x => partialDeriv j f (x - x₀) := by
  funext x
  simp only [partialDeriv, update_sub]
  rw [deriv_comp_sub_const (fun r => f (Function.update (x - x₀) j r)) (x₀ j) (x j)]
  rfl

theorem normLaplacian_comp_sub (f : (Fin d → ℝ) → ℂ) (x₀ x : Fin d → ℝ) :
    normLaplacian (fun y => f (y - x₀)) x = normLaplacian f (x - x₀) := by
  simp only [normLaplacian, partialDeriv_comp_sub]

/-! ### The symmetries of (NLS) -/

section Solutions

variable {L α T : ℝ} {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ}

/-- Gauge invariance: `e^{iθ} u` solves (NLS) with data `e^{iθ} c`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.gauge (hu : IsSmoothNLSSolution L α T c u) (θ : ℝ) :
    IsSmoothNLSSolution L α T (fun n => exp ((θ : ℂ) * I) * c n)
      (fun t x => exp ((θ : ℂ) * I) * u t x) := by
  set z := exp ((θ : ℂ) * I) with hz
  have hzn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  refine ⟨contDiffOn_const.mul hu.1, fun t ht x j => by simp only [hu.2.1 t ht x j],
    fun n => by rw [torusFourierCoeff_const_mul, hu.2.2.1 n], fun t ht x => ?_⟩
  rw [derivWithin_const_mul z (hu.differentiableWithinAt ht x), normLaplacian_const_mul,
    norm_mul, hzn, one_mul]
  linear_combination z * hu.2.2.2 t ht x

/-- Space translation invariance: `u(· - x₀)` solves (NLS) with data
`e^{-2πi⟨n/L, x₀⟩} cₙ = torusChar L n (-x₀) cₙ`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.translate (hL : 0 < L) (hT : 0 ≤ T)
    (hu : IsSmoothNLSSolution L α T c u) (x₀ : Fin d → ℝ) :
    IsSmoothNLSSolution L α T (fun n => torusChar L n (-x₀) * c n)
      (fun t x => u t (x - x₀)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  refine ⟨?_, fun t ht x j => ?_, fun n => ?_, fun t ht x => ?_⟩
  · have hA : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => (p.1, p.2 - x₀)) (Icc 0 T ×ˢ univ) :=
      (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contDiffOn
    exact hu.1.comp hA (fun p hp => ⟨hp.1, mem_univ _⟩)
  · simp only
    rw [add_sub_right_comm, hu.2.1 t ht (x - x₀) j]
  · have h := torusFourierCoeff_comp_add hL (hu.isTorusPeriodic h0) (-x₀) n
    simp only [← sub_eq_add_neg] at h
    rw [h, hu.2.2.1 n]
  · simp only
    rw [normLaplacian_comp_sub]
    exact hu.2.2.2 t ht (x - x₀)

theorem mem_smoothDataSet_gauge_iff (θ : ℝ) :
    (fun n => exp ((θ : ℂ) * I) * c n) ∈ smoothDataSet L α T ↔ c ∈ smoothDataSet L α T := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun t x => exp (((-θ : ℝ) : ℂ) * I) * u t x, ?_⟩
    have h := hu.gauge (-θ)
    have hc : (fun n => exp (((-θ : ℝ) : ℂ) * I) * (exp ((θ : ℂ) * I) * c n)) = c := by
      funext n
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      simp
    rwa [hc] at h
  · rintro ⟨u, hu⟩
    exact ⟨_, hu.gauge θ⟩

theorem mem_smoothDataSet_translate_iff (hL : 0 < L) (hT : 0 ≤ T) (x₀ : Fin d → ℝ) :
    (fun n => torusChar L n (-x₀) * c n) ∈ smoothDataSet L α T ↔ c ∈ smoothDataSet L α T := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun t x => u t (x - -x₀), ?_⟩
    have h := hu.translate hL hT (-x₀)
    have hc : (fun n => torusChar L n (-(-x₀)) * (torusChar L n (-x₀) * c n)) = c := by
      funext n
      rw [← mul_assoc, ← torusChar_add, neg_neg, add_neg_cancel]
      simp [torusChar]
    rwa [hc] at h
  · rintro ⟨u, hu⟩
    exact ⟨_, hu.translate hL hT x₀⟩

end Solutions

/-! ### The solvability event -/

section Event

variable {Ω : Type*} {L α T : ℝ} {φin : Mom d → ℝ} {g : (Fin d → ℤ) → Ω → ℂ}

/-- Gauge symmetry of the solvability event: rotating the random coefficients does not change
`solvableEvent` (TARGET L567–L569). -/
theorem solvableEvent_gauge (θ : ℝ) :
    solvableEvent L α T φin (fun n o => exp ((θ : ℂ) * I) * g n o) =
      solvableEvent L α T φin g := by
  ext o
  simp only [solvableEvent_eq_preimage, mem_preimage]
  have h : initialCoeff L φin (fun n o => exp ((θ : ℂ) * I) * g n o) o =
      fun n => exp ((θ : ℂ) * I) * initialCoeff L φin g o n := by
    funext n
    simp only [initialCoeff]
    ring
  rw [h, mem_smoothDataSet_gauge_iff]

/-- Space-translation symmetry of the solvability event: modulating the random coefficients by
`e^{-2πi⟨n/L, x₀⟩}` does not change `solvableEvent` (TARGET L567–L569). -/
theorem solvableEvent_translate (hL : 0 < L) (hT : 0 ≤ T) (x₀ : Fin d → ℝ) :
    solvableEvent L α T φin (fun n o => torusChar L n (-x₀) * g n o) =
      solvableEvent L α T φin g := by
  ext o
  simp only [solvableEvent_eq_preimage, mem_preimage]
  have h : initialCoeff L φin (fun n o => torusChar L n (-x₀) * g n o) o =
      fun n => torusChar L n (-x₀) * initialCoeff L φin g o n := by
    funext n
    simp only [initialCoeff]
    ring
  rw [h, mem_smoothDataSet_translate_iff hL hT]

end Event

/-! ### The reduced coefficients -/

theorem massAvg_const_mul {L : ℝ} {z : ℂ} (hz : ‖z‖ = 1) (f : (Fin d → ℝ) → ℂ) :
    massAvg L (fun x => z * f x) = massAvg L f := by
  simp only [massAvg, norm_mul, hz, one_mul]

theorem massAvg_comp_sub {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hp : IsTorusPeriodic L f)
    (x₀ : Fin d → ℝ) : massAvg L (fun x => f (x - x₀)) = massAvg L f := by
  simp only [massAvg, sub_eq_add_neg]
  rw [setIntegral_Icc_comp_add hL (hp.comp fun z => ‖z‖ ^ 2) (-x₀)]

/-- Gauge law of the reduced coefficients: `a(e^{iθ}u) = e^{iθ} a(u)`. -/
theorem reducedCoeff_gauge (L γ δ θ : ℝ) (u : ℝ → (Fin d → ℝ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    reducedCoeff L γ δ (fun s x => exp ((θ : ℂ) * I) * u s x) t n =
      exp ((θ : ℂ) * I) * reducedCoeff L γ δ u t n := by
  simp only [reducedCoeff, torusFourierCoeff_wickGauge,
    massAvg_const_mul (Complex.norm_exp_ofReal_mul_I θ), torusFourierCoeff_const_mul]
  ring

/-- Translation law of the reduced coefficients: `a(u(· - x₀))ₙ = e^{-2πi⟨n/L, x₀⟩} a(u)ₙ`. -/
theorem reducedCoeff_translate {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {u : ℝ → (Fin d → ℝ) → ℂ}
    (x₀ : Fin d → ℝ) (t : ℝ) (hp0 : IsTorusPeriodic L (u 0))
    (hp : IsTorusPeriodic L (u (δ * kineticTime (L ^ (-γ)) * t))) (n : Fin d → ℤ) :
    reducedCoeff L γ δ (fun s x => u s (x - x₀)) t n =
      torusChar L n (-x₀) * reducedCoeff L γ δ u t n := by
  simp only [reducedCoeff, torusFourierCoeff_wickGauge]
  rw [massAvg_comp_sub hL hp0]
  have h := torusFourierCoeff_comp_add hL hp (-x₀) n
  simp only [← sub_eq_add_neg] at h
  rw [h]
  ring

end WaveTurbulence.NLS
