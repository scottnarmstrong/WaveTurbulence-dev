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

/-- Regroup the actual real coordinate function into its coarse independent factors. -/
@[expose] noncomputable def coarsenedCoordinateGrouping {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B) (C : A → Type*) [∀ a, Fintype (C a)] :
    ((Σ a : A, C a) → ℝ) ≃ᵐ ((b : B) → CoarsenedCoordinate g C b → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (coarsenedCoordinateEquiv g C).symm).trans
    (MeasurableEquiv.piCurry (fun (b : B) (_ : CoarsenedCoordinate g C b) => ℝ))

/-- Coarsening preserves the literal product Lebesgue measure. -/
theorem volume_preserving_coarsenedCoordinateGrouping {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B) (C : A → Type*) [∀ a, Fintype (C a)] :
    MeasurePreserving (coarsenedCoordinateGrouping g C) volume volume := by
  exact (volume_measurePreserving_piCurry (ι := B) (κ := CoarsenedCoordinate g C)).comp
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (coarsenedCoordinateEquiv g C).symm)

/-- Every grouped coordinate is exactly its original coordinate, including nontrivial fibers. -/
theorem coarsenedCoordinateGrouping_apply {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B) (C : A → Type*) [∀ a, Fintype (C a)] (u : (Σ a : A, C a) → ℝ)
    (b : B) (a : A) (ha : g a = b) (j : C a) :
    coarsenedCoordinateGrouping g C u b ⟨⟨a,ha⟩,j⟩ = u ⟨a,j⟩ := by
  cases ha
  rfl

/-- The sum of the coarse arities is exactly the old total coordinate count. -/
theorem sum_card_coarsenedCoordinate {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B) (C : A → Type*) [∀ a, Fintype (C a)] :
    (∑ b : B, Fintype.card (CoarsenedCoordinate g C b)) = ∑ a : A, Fintype.card (C a) := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (coarsenedCoordinateEquiv g C)

end WaveTurbulence.Sumint
