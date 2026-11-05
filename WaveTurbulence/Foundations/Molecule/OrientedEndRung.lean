/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIILowerParent
public import WaveTurbulence.Foundations.Molecule.DartGeometry

/-! # Orienting an actual type-II rung by the lower parent

TARGET molecpl (2), “up to symmetry”: choose the first rung atom to be
the actual parent of the lower joint, retaining all actual incidence rows.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree

/-- Interchange the two actual rung atoms, without changing their dart rows. -/
@[expose] def EndRungData.swap {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {S : Finset V} {a b : V} (R : EndRungData M S a b) :
    EndRungData M S a b where
  left := R.right
  right := R.left
  nextLeft := R.nextRight
  nextRight := R.nextLeft
  left_mem := R.right_mem
  right_mem := R.left_mem
  nextLeft_mem := R.nextRight_mem
  nextRight_mem := R.nextLeft_mem
  distinct := R.distinct.symm
  left_ne_upper := R.right_ne_upper
  left_ne_lower := R.right_ne_lower
  right_ne_upper := R.left_ne_upper
  right_ne_lower := R.left_ne_lower
  nextLeft_ne_left := R.nextRight_ne_right
  nextLeft_ne_right := R.nextRight_ne_left
  nextRight_ne_left := R.nextLeft_ne_right
  nextRight_ne_right := R.nextLeft_ne_left
  left_row := R.right_row
  right_row := R.left_row

/-- Every current CL type-II vine admits the parent-oriented actual rung data. -/
theorem typeII_oriented_end_rung {w : ℕ} (G : Garden w)
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ (R : EndRungData G.molecule S a b) (hn : b.1.2 ≠ []),
      GNode.parent b.toNode hn = R.left := by
  obtain ⟨R⟩ := garden_typeII_end_rung G hV
  obtain ⟨hn,hp | hp⟩ := R.lower_parent G hV.1 hCL
  · exact ⟨R,hn,hp⟩
  · exact ⟨R.swap,hn,hp⟩

end WaveTurbulence.Molecpl
