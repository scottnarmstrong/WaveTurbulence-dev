/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentProduct
import Mathlib.Tactic

/-! # Explicit component projection hull of an admissibility predicate

The hull records precisely the weakening to independent component tests.
It is not identified with an arbitrary cross-component predicate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbSideAdmissibility (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) (ζ : AppbSideDart M S → (Fin d → ℤ)) : Prop :=
  ∃ κ, A κ ∧ appbSideLabels M S κ = ζ

def appbComponentHull (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) : (D → (Fin d → ℤ)) → Prop :=
  appbSeparatedAdmissibility M S (appbSideAdmissibility M S A)
    (appbSideAdmissibility M (M.atoms \ S) A)

theorem appb_mem_componentHull (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) {κ : D → (Fin d → ℤ)} (hκ : A κ) :
    appbComponentHull M S A κ := ⟨⟨κ,hκ,rfl⟩,⟨κ,hκ,rfl⟩⟩

end WaveTurbulence.Mole
