/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LatticeCoordinates
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Actual regular couples supply the structural leaf-coordinate data

This discharges the generic localization infrastructure's structural input
from the proved C2 integer matrices. No Fourier or analytic bound is a
field of the resulting IntegerLeafCoordinates.
-/

@[expose] public section
namespace WaveTurbulence.RegAsymp
open Links Matrix

/-- Enumerate all actual plus leaves, with the source cardinality2n+1. -/
noncomputable def plusLeafEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) :
    Fin (2*Q.links.length+1) ≃ PlusLeaf G :=
  (Fintype.equivFinOfCardEq (by
    rw [card_plusLeaf hQ hG]
    simp only [LinkCoord,Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
    omega)).symm

/-- For a source couple every positive leaf is an actual input. -/
theorem inputLeaves_eq_plusLeaves {G : Garden 2} (hG : IsCouple G) : inputLeaves G = plusLeaves G := by
  ext ℓ
  simp only [inputLeaves,plusLeaves,Finset.mem_filter,Finset.mem_univ,true_and,hG.1 ℓ,and_true]

/-- The literal B1 input product is the product over the proved plus-leaf
enumeration. No multiplicity or unmarked-leaf condition is dropped. -/
theorem prod_inputLeaves_eq_enumerated {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (f : GLeaf G.tree → ℂ) :
    (∏ ℓ ∈ inputLeaves G, f ℓ) = ∏ i, f (plusLeafEquiv hQ hG i).val := by
  rw [inputLeaves_eq_plusLeaves hG]
  calc
    _ = ∏ ℓ : PlusLeaf G, f ℓ.val := Finset.prod_subtype _ (fun ℓ => mem_plusLeaves ℓ) f
    _ = _ := ((plusLeafEquiv hQ hG).prod_comp (fun ℓ : PlusLeaf G => f ℓ.val)).symm

end WaveTurbulence.RegAsymp
