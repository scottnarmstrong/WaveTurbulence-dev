/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.List.Lex
/-! Unique least keys on finite nonempty candidate carriers. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA

/-- An injective key on a finite nonempty carrier has one least candidate. -/
theorem existsUnique_least_key {A K : Type*} [Finite A] [Nonempty A] [LinearOrder K]
    (key : A → K) (hinj : Function.Injective key) : ∃! x, ∀ y, key x ≤ key y := by
  obtain ⟨x, hx⟩ := Finite.exists_min key
  exact ⟨x, hx, fun y hy => hinj (le_antisymm (hy x) (hx y))⟩

/-- The unique least candidate, constructed only after proving its uniqueness. -/
noncomputable def leastKey {A K : Type*} [Finite A] [Nonempty A] [LinearOrder K]
    (key : A → K) (hinj : Function.Injective key) : A :=
  (existsUnique_least_key key hinj).choose

theorem leastKey_spec {A K : Type*} [Finite A] [Nonempty A] [LinearOrder K]
    (key : A → K) (hinj : Function.Injective key) (y : A) :
    key (leastKey key hinj) ≤ key y := (existsUnique_least_key key hinj).choose_spec.1 y

theorem leastKey_unique {A K : Type*} [Finite A] [Nonempty A] [LinearOrder K]
    (key : A → K) (hinj : Function.Injective key) (x : A)
    (hx : ∀ y, key x ≤ key y) : x = leastKey key hinj :=
  (existsUnique_least_key key hinj).choose_spec.2 x hx

end WaveTurbulence.VineA
