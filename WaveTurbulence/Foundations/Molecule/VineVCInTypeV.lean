/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
public import WaveTurbulence.Foundations.Molecule.VineCentralV
public import WaveTurbulence.Foundations.Molecule.VineSmallVC
import Mathlib.Tactic

/-! # Every VC contained in type V is small or the entire vine -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc's type-V structural case, without any decoration or
gap hypothesis: every nested VC is one/two double bonds or the entire type V.
Selecting either outer joint forces selection of the other via their actual
joint bond; selecting both forces the entire connected block. -/
theorem VC_in_typeV (M : Molecule V D) (hM : M.IsMolecule)
    {A S : Finset V} {a b x y : V} (hV : M.IsVine .V S a b) (hA : IsVC M A x y) (hAS : A ⊆ S) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y := by
  have hab := typeV_joints_adj hV
  by_cases hboth : a ∈ A ∧ b ∈ A
  · have he := nested_blocks_both_joints_eq M hA.1 hV.1 (isVine_connected hV) hAS hboth.1 hboth.2
    subst A
    exact Or.inr (Or.inr (isVine_rejoint hV hA.1))
  · have ha : a ∉ A := by
      intro ha
      exact hboth ⟨ha,nested_block_joint_adj_mem M hA.1 hV.1 hAS ha (Or.inl rfl) hV.1.2.2.1 hab⟩
    have hb : b ∉ A := by
      intro hb
      exact hboth ⟨nested_block_joint_adj_mem M hA.1 hV.1 hAS hb (Or.inr rfl) hV.1.2.1
        (Mole.adj_symmetric M hab),hb⟩
    have hc : A.card ≤ 3 := by
      by_cases hsmall : A.card ≤ 2
      · omega
      · obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
        exact typeV_inner_card_le_three M hM R hS hA.1 (isVC_connected hA) hAS (by omega) ha hb
    rcases isVC_doubleChain_of_card_le_three hA hc with hD | hD
    · exact Or.inl hD
    · exact Or.inr (Or.inl hD)

end WaveTurbulence.Vine
