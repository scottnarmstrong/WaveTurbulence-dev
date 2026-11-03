/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierStepInterpolation
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Tactic

/-!
# Fourier interpolation for integrable simple functions

Every integrable simple function has finitely many nonzero, finite-measure
fibers. Expressing those fibers as a disjoint step function turns the
finite-dimensional interpolation theorem into a Fourier pairing bound.
-/

public section

open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

/-- Represent an integrable simple function by disjoint finite-measure cells.
The zero fiber is omitted, so no finiteness assumption on the ambient measure is needed. -/
theorem simpleFunc_exists_finiteStep {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : SimpleFunc α ℂ) (hf : Integrable f μ) :
    ∃ (n : ℕ) (A : Fin n → Set α) (a : Fin n → ℂ),
      (∀ i, MeasurableSet (A i)) ∧ (∀ i, μ (A i) ≠ ∞) ∧
        Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (f : α → ℂ) = finiteStepFunction A a := by
  classical
  let I := ↥(f.range.erase 0)
  let e := Fintype.equivFin I
  let a := fun i : Fin (Fintype.card I) => ((e.symm i : I) : ℂ)
  let A := fun i : Fin (Fintype.card I) => f ⁻¹' {a i}
  have ha (i : Fin (Fintype.card I)) : a i ≠ 0 :=
    Finset.mem_erase.mp (e.symm i).property |>.1
  have hai : Function.Injective a := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hai ((Set.mem_singleton_iff.mp hxi).symm.trans (Set.mem_singleton_iff.mp hxj)))
  refine ⟨Fintype.card I, A, a, (fun i => f.measurableSet_fiber (a i)),
    (fun i => (SimpleFunc.integrable_iff.mp hf (a i) (ha i)).ne), hd, ?_⟩
  funext x
  by_cases hx : f x = 0
  · have hxA (i : Fin (Fintype.card I)) : x ∉ A i := by
      intro hi
      exact ha i ((Set.mem_singleton_iff.mp hi).symm.trans hx)
    simp [finiteStepFunction, hxA, hx]
  · let y : I := ⟨f x, Finset.mem_erase.mpr ⟨hx, f.mem_range_self x⟩⟩
    let i := e y
    have hai' : a i = f x := by simp [a, i, y]
    have hxi : x ∈ A i := by simp [A, hai']
    unfold finiteStepFunction
    rw [Finset.sum_eq_single i]
    · simp [hxi, hai']
    · intro j _ hji
      have hxj : x ∉ A j := fun hj => Set.disjoint_left.mp (hd hji) hj hxi
      simp [hxj]
    · simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- TARGET L2370: bilinear Hausdorff–Young on integrable simple functions,
with constant exactly one. -/
theorem fourier_pairing_simple {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (f g : SimpleFunc V ℂ) (hf : Integrable f) (hg : Integrable g) :
    ‖∫ ξ, 𝓕 (f : V → ℂ) ξ * g ξ‖ ≤
      lpNorm f (ENNReal.ofReal p) volume * lpNorm g (ENNReal.ofReal p) volume := by
  obtain ⟨n, A, a, hA, hμA, hdA, heA⟩ := simpleFunc_exists_finiteStep f hf
  obtain ⟨m, B, b, hB, hμB, hdB, heB⟩ := simpleFunc_exists_finiteStep g hg
  rw [heA, heB]
  exact fourier_pairing_finite_steps A hA hμA hdA B hB hμB hdB hp1 hp2 a b

end WaveTurbulence.Fourier
