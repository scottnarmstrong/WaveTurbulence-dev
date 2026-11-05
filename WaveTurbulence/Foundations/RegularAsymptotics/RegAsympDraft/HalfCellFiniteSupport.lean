/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFiniteLattice

/-! # Absolute summability of actual finite-cell lattice pullbacks -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset

/-- An injective coordinate restriction preserves the actual finite
lattice support, for arbitrary complex phase values. -/
theorem hasFiniteSupport_halfCell_lattice_pullback {d n : ℕ} {U : Type*}
    {L : ℝ} (hL : 0 < L) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d)
    (ρ : U → (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ))
    (hρ : Function.Injective ρ) (P : U → ℂ) :
    Function.HasFiniteSupport (fun u => halfCellAmplitude z β γ
      (fun j => latticePoint L ((ρ u).1 j)) (fun j => latticePoint L ((ρ u).2 j))*P u) := by
  apply (Set.Finite.preimage hρ.injOn (halfCellArrayLatticeBox L z).finite_toSet).subset
  intro u hu
  exact mem_halfCellArrayLatticeBox hL z β γ (ρ u) (mul_ne_zero_iff.mp hu).1

/-- The resulting source series is absolutely summable, so all finite
coordinate decompositions can use the usual complex Fubini theorems. -/
theorem summable_halfCell_lattice_pullback {d n : ℕ} {U : Type*}
    {L : ℝ} (hL : 0 < L) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d)
    (ρ : U → (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ))
    (hρ : Function.Injective ρ) (P : U → ℂ) :
    Summable (fun u => halfCellAmplitude z β γ
      (fun j => latticePoint L ((ρ u).1 j)) (fun j => latticePoint L ((ρ u).2 j))*P u) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_halfCell_lattice_pullback hL z β γ ρ hρ P)

end WaveTurbulence.RegAsymp
