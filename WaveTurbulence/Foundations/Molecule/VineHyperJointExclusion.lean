/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperRungMembership
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
import Mathlib.Tactic

/-! # Hyper-block subsets avoid both ordinary outer block joints -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A hyper-block inside an ordinary block cannot contain either outer
joint: its minimum internal degree is three, while those joints have degree
two even in the larger block. No gap or template premise is needed. -/
theorem hyperBlock_outer_joints_absent (M : Molecule V D)
    {S A : Finset V} {a b x y : V} (hS : M.IsBlock S a b)
    (hH : Mole.IsHyperBlock M A x y) (hAS : A ⊆ S) : a ∉ A ∧ b ∉ A := by
  obtain ⟨ha,hb⟩ := Mole.block_joint_degrees M hS
  constructor
  · intro hh
    have hmin := hyperBlock_degree_ge_three M hH hh
    have hle := degIn_mono M hAS a
    omega
  · intro hh
    have hmin := hyperBlock_degree_ge_three M hH hh
    have hle := degIn_mono M hAS b
    omega

end WaveTurbulence.Vine
