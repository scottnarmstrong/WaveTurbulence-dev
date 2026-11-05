/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LatticeCoordinates
public import WaveTurbulence.Foundations.Incoh.IntegerLeafCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Actual regular couples supply the structural leaf-coordinate data

This discharges the generic localization infrastructure's structural input
from the proved C2 integer matrices. No Fourier or analytic bound is a
field of the resulting IntegerLeafCoordinates.
-/

@[expose] public section
namespace WaveTurbulence.RegAsymp
open Links Matrix

/-- Enumerate the actual root first, then the independent x/y coordinates. -/
def linkCoordinateEquiv (Q : RegCpl) :
    Fin (2*Q.links.length+1) ≃ LinkCoord Q :=
  (finSuccEquiv (2*Q.links.length)).trans
    (Equiv.optionCongr ((finCongr (Nat.mul_comm 2 Q.links.length)).trans finProdFinEquiv.symm))

@[simp] theorem linkCoordinateEquiv_zero (Q : RegCpl) : linkCoordinateEquiv Q 0 = none := by
  rfl

/-- Enumerate all actual plus leaves, with the source cardinality2n+1. -/
noncomputable def plusLeafEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) :
    Fin (2*Q.links.length+1) ≃ PlusLeaf G :=
  (Fintype.equivFinOfCardEq (by
    rw [card_plusLeaf hQ hG]
    simp only [LinkCoord,Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
    omega)).symm

/-- The actual source coefficient rows, reindexed once, give precisely the
integer-coordinate carrier used by the proved leaf Fourier bounds. -/
theorem exists_leafCoordinateData {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) :
    ∃ P : Incoh.IntegerLeafCoordinates Q.links.length,
      ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V), IsDecoration G κ →
        (∀ i, κ (plusLeafEquiv hQ hG i).val.toNode =
          ∑ j, P.forward i j • linkCoords Q κ (linkCoordinateEquiv Q j)) ∧
        (∀ j, linkCoords Q κ (linkCoordinateEquiv Q j) =
          ∑ i, P.backward j i • κ (plusLeafEquiv hQ hG i).val.toNode) := by
  classical
  obtain ⟨T,S,hTS,hST,hroot,hrow,hdec⟩ := incoh_unimodular hQ hG
  let eL := plusLeafEquiv hQ hG
  let eC := linkCoordinateEquiv Q
  let P : Incoh.IntegerLeafCoordinates Q.links.length :=
    { forward := T.submatrix eL eC
      backward := S.submatrix eC eL
      forward_mul_backward := by rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_one_equiv]
      backward_mul_forward := by rw [Matrix.submatrix_mul_equiv,hST,Matrix.submatrix_one_equiv]
      root_column := by
        intro i
        change T (eL i) (linkCoordinateEquiv Q 0) = 1
        rw [linkCoordinateEquiv_zero]
        exact hroot _
      root_row_mem := by
        intro i
        change S (linkCoordinateEquiv Q 0) (eL i) ∈ _
        rw [linkCoordinateEquiv_zero,hrow]
        exact incohSigma_mem (eL i).val }
  refine ⟨P,?_⟩
  intro V _ κ hκ
  obtain ⟨hf,hb⟩ := hdec V κ hκ
  constructor
  · intro i
    change κ (eL i).val.toNode = ∑ j, T (eL i) (eC j) • linkCoords Q κ (eC j)
    exact (hf (eL i)).trans (eC.sum_comp (fun j => T (eL i) j • linkCoords Q κ j)).symm
  · intro j
    change linkCoords Q κ (eC j) = ∑ i, S (eC j) (eL i) • κ (eL i).val.toNode
    exact (hb (eC j)).trans (eL.sum_comp (fun i => S (eC j) i • κ i.val.toNode)).symm

/-- The actual integer rows, selected from the proved source construction. -/
noncomputable def leafCoordinateData {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) : Incoh.IntegerLeafCoordinates Q.links.length :=
  Classical.choose (exists_leafCoordinateData hQ hG)

/-- All selected rows recover the actual source leaf values, for every
additive carrier; this is independent of any analytic input. -/
theorem leafCoordinateData_spec {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) :
    ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V), IsDecoration G κ →
      (∀ i, κ (plusLeafEquiv hQ hG i).val.toNode =
        ∑ j, (leafCoordinateData hQ hG).forward i j • linkCoords Q κ (linkCoordinateEquiv Q j)) ∧
      (∀ j, linkCoords Q κ (linkCoordinateEquiv Q j) =
        ∑ i, (leafCoordinateData hQ hG).backward j i • κ (plusLeafEquiv hQ hG i).val.toNode) :=
  Classical.choose_spec (exists_leafCoordinateData hQ hG)

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
