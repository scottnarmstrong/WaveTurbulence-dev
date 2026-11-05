/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainCounts
import Mathlib.Tactic

/-! # Identification of VCs on at most three atoms -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A VC on at most three atoms is exactly one or two double-bond
ingredients. This converts a proved size bound into the source shapes. -/
theorem isVC_doubleChain_of_card_le_three {M : Molecule V D} {A : Finset V} {x y : V}
    (hVC : IsVC M A x y) (hc : A.card ≤ 3) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 := by
  obtain ⟨_hB,n,hC⟩ := hVC
  have hp := chain_pos hC
  have hD := chain_doubleChain_of_card_lt_four hC (by omega)
  have hcount := doubleChain_card hD
  have hn : n=1 ∨ n=2 := by omega
  rcases hn with rfl | rfl
  · exact Or.inl hD
  · exact Or.inr hD

end WaveTurbulence.Vine
