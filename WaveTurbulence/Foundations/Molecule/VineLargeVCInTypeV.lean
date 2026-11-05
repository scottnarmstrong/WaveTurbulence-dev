/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVCInTypeV
import Mathlib.Tactic

/-! # A large VC inside type V is the entire branch -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A nested VC with more than three atoms in type V equals the whole
outer vine, with no gap assumption. This records the equality implicit
in the structural classification proof. -/
theorem large_VC_in_typeV_eq (M : Molecule V D) (hM : M.IsMolecule)
    {A S : Finset V} {a b x y : V} (hV : M.IsVine .V S a b)
    (hA : IsVC M A x y) (hAS : A ⊆ S) (hcard : 3<A.card) : A=S := by
  have hab := typeV_joints_adj hV
  by_cases hboth : a ∈ A ∧ b ∈ A
  · exact nested_blocks_both_joints_eq M hA.1 hV.1 (isVine_connected hV) hAS hboth.1 hboth.2
  · have ha : a ∉ A := by
      intro ha
      exact hboth ⟨ha,nested_block_joint_adj_mem M hA.1 hV.1 hAS ha (Or.inl rfl) hV.1.2.2.1 hab⟩
    have hb : b ∉ A := by
      intro hb
      exact hboth ⟨nested_block_joint_adj_mem M hA.1 hV.1 hAS hb (Or.inr rfl) hV.1.2.1
        (Mole.adj_symmetric M hab),hb⟩
    obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
    have hc := typeV_inner_card_le_three M hM R hS hA.1 (isVC_connected hA) hAS (by omega) ha hb
    omega

/-- Every type-V vine has more than three atoms, including arbitrary
rung counts in its source slot. -/
theorem typeV_card_gt_three {M : Molecule V D} {A : Finset V} {x y : V}
    (h : M.IsVine .V A x y) : 3<A.card := by
  obtain ⟨k,_hk,hc,_hb⟩ := isVine_counts h
  norm_num [VineType.template] at hc
  omega

end WaveTurbulence.Vine
