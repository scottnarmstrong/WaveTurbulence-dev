/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
import Mathlib.Tactic

/-! # Exact bond multiplicities from the actual removed-edge enumeration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Every bond at a deleted atom is enumerated, so its multiplicity is an
exact finite sum over the input edge table, including parallel copies. -/
theorem bondsBetween_eq_local_sum {a : V} (ha : a ∈ r.removedAtoms) (b : V) :
    M.bondsBetween a b = ∑ i : Fin P.edges.length,
      if M.ends (r.edge i).val = s(a,b) then 1 else 0 := by
  rw [r.removedBond_sum (fun x => if M.ends x = s(a,b) then 1 else 0)]
  simp only [sum_boole]
  unfold Molecule.bondsBetween
  congr 1
  symm
  ext x
  simp only [appbRemovedBonds,mem_filter]
  constructor
  · rintro ⟨⟨hx,hd⟩,he⟩
    exact ⟨hx,he⟩
  · rintro ⟨hx,he⟩
    refine ⟨⟨hx,?_⟩,he⟩
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl (h.1.symm ▸ ha)
    · exact Or.inr (h.2.symm ▸ ha)

end AppbRealization
end WaveTurbulence.Mole
