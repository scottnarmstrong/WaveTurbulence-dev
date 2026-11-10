/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootCumulative
public import WaveTurbulence.Foundations.Incoh.TriangleSetIntegral
public import WaveTurbulence.Foundations.Incoh.TreeCausalExtension
public import WaveTurbulence.Foundations.Incoh.LocalRootDensity

/-!
# Source agreement of the actual causal tree extension

The constrained source integral equals the triangular integral of its
literal root marginal. Cutoffs equal to one on the source clock boxes
therefore give pointwise agreement, including the external endpoints.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The source root/lone-parent causal constraints. -/
@[expose] def RootCoordinates.causalRootCut {n : ℕ} (R : RootCoordinates n)
    (t : Fin 2 → ℝ) : Set (Fin n → Fin 2 → ℝ) :=
  R.equiv ⁻¹' (causalTriangle (t 0) (t 1) ×ˢ univ)

theorem RootCoordinates.measurableSet_causalRootCut {n : ℕ} (R : RootCoordinates n)
    (t : Fin 2 → ℝ) : MeasurableSet (R.causalRootCut t) :=
  ((measurableSet_causalTriangle _ _).prod MeasurableSet.univ).preimage R.equiv.measurable

/-- The literal normalized source product with its external causal constraints. -/
@[expose] def RootCoordinates.causalKernel {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) : ℂ :=
  normalizedLinkIntegral L γ δ Q (I ∩ R.causalRootCut t)

/-- The actual constrained source integral is the causal root-marginal integral. -/
theorem RootCoordinates.causalKernel_eq_setIntegral {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    R.causalKernel L γ δ Q I t = ∫ u in causalTriangle (t 0) (t 1), R.linkDensity L γ δ Q I u := by
  have hcut := R.measurableSet_causalRootCut t
  have hF := integrable_normalizedLinkIntegrand hL γ δ Q hI hbox
  have heq : normalizedLinkIntegrand L γ δ Q (I ∩ R.causalRootCut t) =
      (R.causalRootCut t).indicator (normalizedLinkIntegrand L γ δ Q I) := by
    funext u
    by_cases hi : u ∈ I <;> by_cases hc : u ∈ R.causalRootCut t <;>
      simp [normalizedLinkIntegrand, hi, hc]
  rw [causalKernel, ← integral_normalizedLinkIntegrand L γ δ Q (hI.inter hcut), heq,
    integral_indicator hcut]
  exact (R.setIntegral_density hF (causalTriangle (t 0) (t 1))).symm

/-- Interior clock cutoffs equal to one on the source box leave the literal marginal unchanged. -/
theorem RootCoordinates.cutoff_linkDensity_eq_self {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {χ : ℝ → ℝ}
    (hχ : ∀ u ∈ R.rootBox Q, ∀ j, χ (u j) = 1) (u : Fin 2 → ℝ) :
    (χ (u 0) : ℂ) * (χ (u 1) : ℂ) * R.linkDensity L γ δ Q I u = R.linkDensity L γ δ Q I u := by
  by_cases hu : u ∈ R.rootBox Q
  · rw [hχ u hu 0, hχ u hu 1]
    simp only [Complex.ofReal_one, one_mul]
  · rw [R.linkDensity_eq_zero_of_notMem_rootBox L γ δ Q hbox hu, mul_zero]

end WaveTurbulence.Incoh
