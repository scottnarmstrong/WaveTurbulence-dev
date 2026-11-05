/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ThreeChildSlots
public import WaveTurbulence.Foundations.Molecule.LowerParentDart
public import WaveTurbulence.Foundations.Molecule.MateBondTypes

/-! # Actual three-child incidence rows for the incomparable type-II case -/

public section
namespace WaveTurbulence.Molecpl
open TTree Vine

/-- Three pairwise distinct values form an injective ordered triple. -/
theorem triple_injective {α : Type*} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (![x,y,z] : Fin 3 → α) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all

variable {w : ℕ} (G : Garden w)

/-- The other rung atom's three displayed incidences are distinct. -/
theorem other_rung_triple_injective {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) : Function.Injective
      (![G.molecule.mate (R.left_row.dart 0),G.molecule.mate (R.left_row.dart 1),
        R.right_row.dart 2] : Fin 3 → GardenDart G) := by
  apply triple_injective
  · intro he
    exact (by decide : (0:Fin 4) ≠ 1) (R.left_row.injective (Mole.mate_injective G.molecule he))
  · intro he
    have hh := congrArg (fun x => G.molecule.atom (G.molecule.mate x)) he
    rw [G.molecule.mate_mate,R.left_row.atom_eq,R.right_row.neighbor_eq] at hh
    exact R.left_ne_lower hh
  · intro he
    have hh := congrArg (fun x => G.molecule.atom (G.molecule.mate x)) he
    rw [G.molecule.mate_mate,R.left_row.atom_eq,R.right_row.neighbor_eq] at hh
    exact R.left_ne_lower hh

/-- In the two-LP rung case all three children of the other rung atom are leaves. -/
theorem other_rung_all_children_leaves {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) (hall : RungAllLP G R) (hlp : LowerLP G R) :
    ∀ i : Fin 3, ∃ l : GLeaf G.tree, l.toNode = R.right.child i := by
  let D : Fin 3 → GardenDart G :=
    ![G.molecule.mate (R.left_row.dart 0),G.molecule.mate (R.left_row.dart 1),R.right_row.dart 2]
  apply three_LP_children G D (other_rung_triple_injective G R)
  · intro i; fin_cases i
    · exact R.left_row.neighbor_eq 0
    · exact R.left_row.neighbor_eq 1
    · exact R.right_row.atom_eq 2
  · intro i; fin_cases i
    · exact not_pc_mate G (hall 0)
    · exact not_pc_mate G (hall 1)
    · have hh := not_pc_mate G hlp
      rw [G.molecule.mate_mate] at hh
      exact hh

end WaveTurbulence.Molecpl
