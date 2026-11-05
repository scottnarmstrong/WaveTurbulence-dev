/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideRailAvoidance
public import WaveTurbulence.Foundations.Molecule.VineSlotProtectedPaths
import Mathlib.Tactic

/-! # Actual type-VII red rail data avoid the removed full side -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The exact source red slot supplies primitive protected rail data,
including zero rung counts. No graph or path classification is assumed. -/
theorem VineRealization.typeVII_red_protected_data {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) :
    ∃ Q : FullRungSequence M kr,(∀ i,Q.u i ∈ S ∧ Q.v i ∈ S) ∧
      (R.f (Q.u 0)=2 ∧ R.f (Q.v 0)=3 ∧
        R.f (Q.u (kr+1))=7 ∧ R.f (Q.v (kr+1))=8) ∧
      (∀ i,1 ≤ i → i ≤ kr → R.f (Q.u i)=(11)+(i-1) ∧
        R.f (Q.v i)=(11)+kr+(i-1)) ∧
      RailAvoidsPiece Q (R.selectedAtoms (sideLabels (11+2*kr) kc))
        (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1 ∧
      (kr=0 → ¬(Q.u 0 ∈ R.selectedAtoms (sideLabels (11+2*kr) kc) ∧
        Q.u (kr+1) ∈ R.selectedAtoms (sideLabels (11+2*kr) kc)) ∧
        ¬(Q.v 0 ∈ R.selectedAtoms (sideLabels (11+2*kr) kc) ∧
        Q.v (kr+1) ∈ R.selectedAtoms (sideLabels (11+2*kr) kc))) := by
  have hloc : VineType.VII.template.slots.zip R.k=
      []++(((2,7),(3,8)),kr)::[(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] := by rw [hks]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports
    [] [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr hloc
  change R.f (Q.u 0)=2 ∧ R.f (Q.v 0)=3 ∧
    R.f (Q.u (kr+1))=7 ∧ R.f (Q.v (kr+1))=8 at hports
  have hlabels' : ∀ i,1 ≤ i → i ≤ kr → R.f (Q.u i)=(11)+(i-1) ∧
      R.f (Q.v i)=(11)+kr+(i-1) := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels
  have H := R.rail_avoids_side_of_labels (11+2*kr) kc (11) kr (by omega)
    Q hmem 2 3 7 8 hports hlabels'
    (by rw [mem_capLabels_iff]; omega) (by rw [mem_capLabels_iff]; omega)
    (by rw [mem_capLabels_iff]; omega) (by rw [mem_capLabels_iff]; omega)
    (by intro j hj; rw [mem_sideLabels_iff]; omega)
  refine ⟨Q,hmem,hports,hlabels',H,?_⟩
  intro _hz
  constructor
  · intro hA
    have hh := (mem_filter.mp hA.1).2
    rw [hports.1,mem_sideLabels_iff] at hh
    omega
  · intro hA
    have hh := (mem_filter.mp hA.1).2
    rw [hports.2.1,mem_sideLabels_iff] at hh
    omega

end WaveTurbulence.Vine
