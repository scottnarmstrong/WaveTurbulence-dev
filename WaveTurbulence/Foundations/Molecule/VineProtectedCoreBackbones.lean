/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSingleBackbones
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! # Single-bond paths avoiding a removed V-side or the DV shared joint bond -/

public section
namespace WaveTurbulence.Vine

/-- Single core edges outside the bonds internal to a removed atom group. -/
@[expose] def protectedCoreBonds (X : VineType) (W : Finset ℕ) : List (ℕ×ℕ) :=
  (singleBonds X.template.bonds).filter fun e => ¬(e.1 ∈ W ∧ e.2 ∈ W)

/-- The type-V retained core has a single-bond path to every noncentral surviving atom. -/
theorem coreV_protected_backbone (v : ℕ) (hv : v ∈ ({0,1,2,3,4,5,6,7} : Finset ℕ)) :
    Relation.EqvGen (EdgeAdj (protectedCoreBonds .V {0,1})) 0 v := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 1 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 1 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 7 1 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 5 1 (Relation.EqvGen.rel 7 5 (by decide)) (Relation.EqvGen.trans 5 3 1 (Relation.EqvGen.rel 5 3 (by decide)) ((Relation.EqvGen.rel 3 1 (by decide))))))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact Relation.EqvGen.trans 0 2 3 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 3 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 3 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 7 3 (Relation.EqvGen.rel 6 7 (by decide)) (Relation.EqvGen.trans 7 5 3 (Relation.EqvGen.rel 7 5 (by decide)) ((Relation.EqvGen.rel 5 3 (by decide)))))))
  · exact Relation.EqvGen.trans 0 2 4 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 4 (by decide)))
  · exact Relation.EqvGen.trans 0 2 5 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 5 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 5 (Relation.EqvGen.rel 4 6 (by decide)) (Relation.EqvGen.trans 6 7 5 (Relation.EqvGen.rel 6 7 (by decide)) ((Relation.EqvGen.rel 7 5 (by decide))))))
  · exact Relation.EqvGen.trans 0 2 6 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 6 (Relation.EqvGen.rel 2 4 (by decide)) ((Relation.EqvGen.rel 4 6 (by decide))))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 4 7 (Relation.EqvGen.rel 2 4 (by decide)) (Relation.EqvGen.trans 4 6 7 (Relation.EqvGen.rel 4 6 (by decide)) ((Relation.EqvGen.rel 6 7 (by decide)))))

/-- The type-VII retained core has a single-bond path to every noncentral surviving atom. -/
theorem coreVII_protected_backbone (v : ℕ) (hv : v ∈ ({0,1,2,3,7,8,9,10} : Finset ℕ)) :
    Relation.EqvGen (EdgeAdj (protectedCoreBonds .VII {4,5,6,7,8})) 0 v := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.EqvGen.refl 0
  · exact Relation.EqvGen.trans 0 2 1 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 1 (Relation.EqvGen.rel 2 7 (by decide)) (Relation.EqvGen.trans 7 9 1 (Relation.EqvGen.rel 7 9 (by decide)) ((Relation.EqvGen.rel 9 1 (by decide)))))
  · exact (Relation.EqvGen.rel 0 2 (by decide))
  · exact (Relation.EqvGen.rel 0 3 (by decide))
  · exact Relation.EqvGen.trans 0 2 7 (Relation.EqvGen.rel 0 2 (by decide)) ((Relation.EqvGen.rel 2 7 (by decide)))
  · exact Relation.EqvGen.trans 0 3 8 (Relation.EqvGen.rel 0 3 (by decide)) ((Relation.EqvGen.rel 3 8 (by decide)))
  · exact Relation.EqvGen.trans 0 2 9 (Relation.EqvGen.rel 0 2 (by decide)) (Relation.EqvGen.trans 2 7 9 (Relation.EqvGen.rel 2 7 (by decide)) ((Relation.EqvGen.rel 7 9 (by decide))))
  · exact Relation.EqvGen.trans 0 3 10 (Relation.EqvGen.rel 0 3 (by decide)) (Relation.EqvGen.trans 3 8 10 (Relation.EqvGen.rel 3 8 (by decide)) ((Relation.EqvGen.rel 8 10 (by decide))))

end WaveTurbulence.Vine
