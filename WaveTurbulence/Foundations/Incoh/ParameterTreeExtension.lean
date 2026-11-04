/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeCommonExtension

/-!
# The actual causal tree extension on arbitrary parameter carriers

Only the parameter carrier changes. The global source/phase identity is
reused slice by slice from the landed common-extension theorem.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Literal causal extension of the actual root marginal, with arbitrary vector parameters. -/
@[expose] def RootCoordinates.parameterTreeCausalExtension {d n : ℕ} {V : Type*}
    (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : V → Fin n → LayerLink d)
    (I : V → Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) (v : V) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (Q v) (I v)) t

/-- The landed global common-extension identity holds for every parameter carrier. -/
theorem parameterTreeCausalExtension_eq_phaseKernel {d n m : ℕ} {V : Type*}
    (R : RootCoordinates n) (Q : V → Fin n → LayerLink d) (T : ∀ v, TreeClockFibers m (Q v))
    (hfirst : ∀ v, R.rootVertex 0 = (T v).selection.coordinates.rootVertex 0)
    (hlast : ∀ v, R.rootVertex 1 = (T v).selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχroot : ∀ v a, a ∈ R.rootBox (Q v) → ∀ j, χ (a j) = 1)
    (hχselected : ∀ v a, a ∈ (T v).selection.coordinates.rootBox (Q v) → ∀ j, χ (a j) = 1) :
    R.parameterTreeCausalExtension χ L γ δ Q (fun v => (T v).timeDomain) =
      fun t v => (T v).causalPhaseKernel χ L γ δ t := by
  funext t v
  have he := treeCausalExtension_eq_phaseKernel R (fun _ : Mom d => Q v) (fun _ => T v)
    (fun _ => hfirst v) (fun _ => hlast v) hL γ δ hmχ hc
    (fun _ => hχroot v) (fun _ => hχselected v)
  exact congrFun (congrFun he t) (0 : Mom d)

end WaveTurbulence.Incoh
