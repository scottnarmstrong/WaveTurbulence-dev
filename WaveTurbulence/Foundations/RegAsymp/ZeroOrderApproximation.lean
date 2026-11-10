/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep

/-! # Exact empty-link number-theory expressions

These identities treat the positive-order Wick trace whose last free
link is removed, without applying a positive-order NT estimate at order zero.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

/-- No lattice variable remains at half-order zero. -/
theorem approxSum_zero_order {d : ℕ} (L μ : ℝ)
    (W : (Fin 0 → Mom d) → (Fin 0 → Mom d) → ℂ) (Ψ : (Fin 0 → ℝ) → ℂ) :
    approxSum L μ W Ψ = W 0 0*Ψ 0 := by
  unfold approxSum
  rw [tsum_eq_single (0,0)]
  · congr 2 <;> apply Subsingleton.elim
  · intro b hb
    exact (hb (Subsingleton.elim _ _)).elim

/-- No singular multiplier remains in the zero-dimensional profile. -/
theorem resProfile_zero_order (J : Finset (Fin 0))
    (Ψ : EuclideanSpace ℝ {j : Fin 0 // j ∉ J} → ℂ) (Ω : Fin 0 → ℝ) :
    resProfile J Ψ Ω = Ψ 0 := by
  have hJ : J = ∅ := Subsingleton.elim _ _
  simp only [resProfile,hJ,Finset.prod_empty,one_mul]
  congr 1
  exact Subsingleton.elim _ _

end WaveTurbulence.RegAsymp
