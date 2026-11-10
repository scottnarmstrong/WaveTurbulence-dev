/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ProductMeasureTools
public import Mathlib.Logic.Equiv.Sum

/-!
# Coarsening finite independent coordinate families

A map from old factors to coarser factors regroups their coordinates
without changing a coordinate or its Lebesgue measure. Empty fibers
are retained as zero-dimensional factors. This permits bounded-arity
cores for the partially fixed source time integrals.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The unchanged old coordinates belonging to one coarse factor. -/
@[expose] def CoarsenedCoordinate {A B : Type*} (g : A → B) (C : A → Type*) (b : B) : Type _ :=
  Σ a : {a : A // g a = b}, C a.1

noncomputable instance {A B : Type*} [Fintype A] (g : A → B) (C : A → Type*) [∀ a, Fintype (C a)] (b : B) :
    Fintype (CoarsenedCoordinate g C b) := inferInstanceAs (Fintype (Σ a : {a : A // g a = b}, C a.1))

/-- Exact coordinate permutation from coarse fibers back to the old factor coordinates. -/
@[expose] def coarsenedCoordinateEquiv {A B : Type*} (g : A → B) (C : A → Type*) :
    (Σ b : B, CoarsenedCoordinate g C b) ≃ (Σ a : A, C a) where
  toFun z := ⟨z.2.1.1,z.2.2⟩
  invFun z := ⟨g z.1,⟨⟨z.1,rfl⟩,z.2⟩⟩
  left_inv := by rintro ⟨b,⟨⟨a,ha⟩,j⟩⟩; cases ha; rfl
  right_inv := by rintro ⟨a,j⟩; rfl

end WaveTurbulence.Sumint
