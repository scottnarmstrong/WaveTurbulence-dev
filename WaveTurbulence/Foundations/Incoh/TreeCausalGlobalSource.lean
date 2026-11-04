/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootCausalSource
public import WaveTurbulence.Foundations.Incoh.CausalOrderingZero

/-!
# Global source identities for the actual causal root marginal

The forward identity keeps the external cutoff factors. A source density
supported on causal root order also gives zero at reversed external clocks.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The canonical extension equals the cutoff-weighted source at forward clocks. -/
theorem RootCoordinates.treeCausalExtension_eq_weighted_source {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) (k : Mom d) (hI : MeasurableSet (I k))
    (hbox : I k ⊆ univ.pi (fun i => linkBox (Q k i))) {χ : ℝ → ℝ}
    (hχ : ∀ u ∈ R.rootBox (Q k), ∀ j, χ (u j) = 1)
    {t : Fin 2 → ℝ} (ht : t 1 ≤ t 0) :
    R.treeCausalExtension χ L γ δ Q I t k =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * R.causalKernel L γ δ (Q k) (I k) t := by
  have he (x y : ℝ) : (χ x : ℂ) * (χ y : ℂ) * R.linkDensity L γ δ (Q k) (I k) ![x, y] =
      R.linkDensity L γ δ (Q k) (I k) ![x, y] :=
    R.cutoff_linkDensity_eq_self L γ δ (Q k) hbox hχ ![x, y]
  change (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    (∫ x in t 1..t 0, ∫ y in t 1..x,
      (χ x : ℂ) * (χ y : ℂ) * R.linkDensity L γ δ (Q k) (I k) ![x, y]) = _
  simp_rw [he]
  rw [integral_triangle_eq_setIntegral (R.integrable_linkDensity hL γ δ (Q k) hI hbox) ht,
    R.causalKernel_eq_setIntegral hL γ δ (Q k) hI hbox t]

/-- Causal support of the literal source gives causal support of its actual root marginal. -/
theorem RootCoordinates.linkDensity_eq_zero_of_reverse {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hord : ∀ w ∈ I, (R.equiv w).1 1 < (R.equiv w).1 0)
    {v : Fin 2 → ℝ} (hv : v 0 ≤ v 1) : R.linkDensity L γ δ Q I v = 0 := by
  unfold linkDensity density
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  have hi : R.equiv.symm (v, u) ∉ I := by
    intro h
    have hh := hord _ h
    rw [MeasurableEquiv.apply_symm_apply] at hh
    exact (not_lt_of_ge hv) hh
  simp only [normalizedLinkIntegrand, indicator_of_notMem hi, mul_zero, Pi.zero_apply]

/-- Reversed external clock pairs give zero for every causally supported source. -/
theorem RootCoordinates.treeCausalExtension_eq_zero_of_reverse {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) (k : Mom d)
    (hord : ∀ w ∈ I k, (R.equiv w).1 1 < (R.equiv w).1 0)
    {t : Fin 2 → ℝ} (ht : t 0 ≤ t 1) : R.treeCausalExtension χ L γ δ Q I t k = 0 := by
  change (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
    Fourier.orderedIntegral 2 (fun v => (χ (v 0) : ℂ) * (χ (v 1) : ℂ) *
      R.linkDensity L γ δ (Q k) (I k) v) (t 0) (t 1) = 0
  rw [orderedIntegral_eq_zero_of_reverse_support 0 _ (fun v hv => by
    rw [R.linkDensity_eq_zero_of_reverse L γ δ (Q k) (I k) hord hv, mul_zero]) ht, mul_zero]

end WaveTurbulence.Incoh
