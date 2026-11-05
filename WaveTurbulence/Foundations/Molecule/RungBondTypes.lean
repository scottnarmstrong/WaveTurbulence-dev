/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafPairPositions
public import WaveTurbulence.Foundations.Molecule.OrientedEndRung

/-! # The two possible PC/LP labelings of a doubled rung

TARGET molecpl: the double bond consists of either two LP bonds or one
PC and one LP bond. Both witnesses are actual garden darts.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Vine

/-- Retain the two doubled incidences of an actual complete rung row. -/
@[expose] def FourIncidences.doublePair {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {c d a b : V} (R : Vine.FourIncidences M c ![d,d,a,b]) :
    TwoIncidences M c d where
  dart := fun i => R.dart ⟨i.val,by omega⟩
  injective := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 4 => k.val) (R.injective he))
  atom_eq := fun i => R.atom_eq _
  neighbor_eq := by
    intro i
    fin_cases i
    · exact R.neighbor_eq 0
    · exact R.neighbor_eq 1

variable {w : ℕ} (G : Garden w)

/-- Every actual doubled bond has precisely one of the two allowed PC/LP patterns. -/
theorem doubled_label_split {a b : GBranch G.tree} (R : TwoIncidences G.molecule a b) :
    (¬ IsPCDart G (R.dart 0) ∧ ¬ IsPCDart G (R.dart 1)) ∨
    (IsPCDart G (R.dart 0) ∧ ¬ IsPCDart G (R.dart 1)) ∨
    (¬ IsPCDart G (R.dart 0) ∧ IsPCDart G (R.dart 1)) := by
  by_cases h0 : IsPCDart G (R.dart 0)
  · have h1 : ¬ IsPCDart G (R.dart 1) := by
      intro h1
      have he := pc_dart_unique G h0 h1 ((R.atom_eq 0).trans (R.atom_eq 1).symm)
        ((R.neighbor_eq 0).trans (R.neighbor_eq 1).symm)
      exact (by decide : (0:Fin 2) ≠ 1) (R.injective he)
    exact Or.inr (Or.inl ⟨h0,h1⟩)
  · by_cases h1 : IsPCDart G (R.dart 1)
    · exact Or.inr (Or.inr ⟨h0,h1⟩)
    · exact Or.inl ⟨h0,h1⟩

end WaveTurbulence.Molecpl
