/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentNormalization
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentCountProduct
import Mathlib.Tactic

/-! # Component factorization of the actual APPB normalized count

Independent component predicates give equality. An arbitrary predicate has
only the upper bound by its explicit component projection hull. No
cross-component compatibility is silently identified with a product.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem linkCountA_mono (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    {A B : (D → (Fin d → ℤ)) → Prop} (P : Finset V → ℝ) (h : ∀ κ,A κ → B κ) :
    appbLinkCountA M L γ δ C1 w A P ≤ appbLinkCountA M L γ δ C1 w B P :=
  mul_le_mul_left (ENat.toENNReal_mono (appbCountE_mono M L γ δ w h)) _

theorem component_linkCountA_product (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (γ : ℝ) (w : Mom d)
    (A1 : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (A2 : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hP : ∀ T,0 ≤ P T) :
    appbLinkCountA M L γ δ C1 w (appbSeparatedAdmissibility M S A1 A2) P =
      appbLinkCountA (appbSideMolecule M S hS) L γ δ C1 w A1 P*
        appbLinkCountA (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ C1 w A2 P := by
  change (appbCountE M L γ δ w (appbSeparatedAdmissibility M S A1 A2) : ℝ≥0∞)*
      ENNReal.ofReal (linkNormalization M d L γ δ C1 P) =
    ((appbCountE (appbSideMolecule M S hS) L γ δ w A1 : ℝ≥0∞)*
      ENNReal.ofReal (linkNormalization (appbSideMolecule M S hS) d L γ δ C1 P))*
    ((appbCountE (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w A2 : ℝ≥0∞)*
      ENNReal.ofReal (linkNormalization (appbSideMolecule M (M.atoms \ S) hS.complement) d L γ δ C1 P))
  rw [component_countE_product M S hS hL γ δ w A1 A2,ENat.toENNReal_mul,
    linkNormalization_closed_side M S hS d hL hδ hC γ P,
    ENNReal.ofReal_mul (linkNormalization_nonneg _ d hL hδ hC γ P hP)]
  ring

/-- Arbitrary constraints may correlate components; projecting them gives
a genuine upper bound with exactly the same normalization constant. -/
theorem component_linkCountA_upper (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L δ C1 : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (γ : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hP : ∀ T,0 ≤ P T) :
    appbLinkCountA M L γ δ C1 w A P ≤
      appbLinkCountA (appbSideMolecule M S hS) L γ δ C1 w (appbSideAdmissibility M S A) P*
        appbLinkCountA (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ C1 w
          (appbSideAdmissibility M (M.atoms \ S) A) P := by
  have hm := linkCountA_mono M L γ δ C1 w (A := A) (B := appbComponentHull M S A) P
    (fun κ hκ => appb_mem_componentHull M S A (κ := κ) hκ)
  exact hm.trans_eq (component_linkCountA_product M S hS hL hδ hC γ w _ _ P hP)

end WaveTurbulence.Mole.AppbAlgorithm
