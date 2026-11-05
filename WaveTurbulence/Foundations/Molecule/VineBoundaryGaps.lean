/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBoundary
import Mathlib.Tactic

/-! # Gap transport across actual two-bond cuts (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module ℝ E] (M : Molecule V D)

/-- Conservation across a two-bond cut with opposite directions identifies
the two boundary labels. This is local cut data, not a gap-equality premise. -/
theorem two_boundary_labels_eq (S : Finset V) (k : D → E)
    (hk : ∀ x, k (M.mate x)=k x)
    (hc : ∀ v ∈ S, ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    (x y : D) (hxy : x ≠ y) (hB : boundary M S = {x,y})
    (hout : M.out x ≠ M.out y) : k x = k y := by
  have hz := boundary_eq_zero M S k hk hc
  rw [hB,sum_pair hxy] at hz
  unfold Molecule.dartSign at hz
  cases hx : M.out x <;> cases hy : M.out y
  · exact False.elim (hout (hx.trans hy.symm))
  · simp only [hx,hy,Bool.false_eq_true,ite_false,ite_true,neg_smul,one_smul] at hz
    have he : k y=k x := eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg,add_comm] using hz)
    exact he.symm
  · simp only [hx,hy,Bool.false_eq_true,ite_false,ite_true,neg_smul,one_smul] at hz
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)
  · exact False.elim (hout (hx.trans hy.symm))

end WaveTurbulence.Vine
