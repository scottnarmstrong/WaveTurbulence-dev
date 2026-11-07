/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9OriginCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.IntegerPrimitivePhaseFactor

/-! # Primitive local phase factors give uniform chart-coordinate witnesses -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

/-- Conditional algebra helper: an integer coefficient row equal to a
signed coordinate row gives the corresponding uniform origin difference. -/
theorem chart_difference_witness_of_coeff (A : FullVineChart M X S a b)
    (p q : Bond M S ⊕ Fin 2) (i : Fin A.indexing.shape.n)
    (hs : chartDifferenceCoeff A p q (.inl i) = 1 ∨ chartDifferenceCoeff A p q (.inl i) = -1)
    (hc : ∀ j, chartDifferenceCoeff A p q j =
      chartDifferenceCoeff A p q (.inl i)*(if j = .inl i then 1 else 0)) :
    (∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      A.chart g r k i = origin M S k.1 g r p-origin M S k.1 g r q) ∨
    (∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      A.chart g r k i = origin M S k.1 g r q-origin M S k.1 g r p) := by
  classical
  rcases hs with hs | hs
  · have hc' (j : ChartAffineIndex A) : chartDifferenceCoeff A p q j = (if j = .inl i then 1 else 0) :=
      (hc j).trans (by rw [hs,one_mul])
    left
    intro E _ g r k
    have he := chartOrigin_difference A g r (A.chart g r k) p q
    rw [Equiv.symm_apply_apply] at he
    have hh : (∑ j : ChartAffineIndex A, chartDifferenceCoeff A p q j •
        Sum.elim (A.chart g r k) (fun _ => r) j) = A.chart g r k i := by
      simp [hc']
    exact (he.trans hh).symm
  · have hc' (j : ChartAffineIndex A) : chartDifferenceCoeff A p q j = -(if j = .inl i then 1 else 0) :=
      (hc j).trans (by rw [hs,neg_one_mul])
    right
    intro E _ g r k
    have he := chartOrigin_difference A g r (A.chart g r k) p q
    rw [Equiv.symm_apply_apply] at he
    have hh : (∑ j : ChartAffineIndex A, chartDifferenceCoeff A p q j •
        Sum.elim (A.chart g r k) (fun _ => r) j) = -A.chart g r k i := by
      simp [hc']
    have hneg := congrArg (fun x : E => -x) (he.trans hh)
    simpa only [neg_sub,neg_neg] using hneg.symm

end WaveTurbulence.VineEstS2
