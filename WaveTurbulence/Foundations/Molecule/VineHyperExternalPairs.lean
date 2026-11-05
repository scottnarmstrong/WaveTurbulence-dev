/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperJointExclusion
public import WaveTurbulence.Foundations.Molecule.VineCoreStemStart
import Mathlib.Tactic

/-! # External neighbors identify a selected hyper-block double pair as its joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A selected hyper-block atom adjacent to an absent atom is a joint. -/
theorem hyperBlock_joint_of_external_neighbor (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x p : V} (hH : Mole.IsHyperBlock M A a b) (hx : x ∈ A)
    (hp : p ∉ A) (hAdj : M.Adj x p) : x=a ∨ x=b := by
  by_contra hh
  have hn : x ≠ a ∧ x ≠ b := not_or.mp hh
  have hd := (Mole.hyperBlock_degrees M hH).2.2 x hx hn.1 hn.2
  obtain ⟨e,hex,hep⟩ := hAdj
  obtain ⟨d,_he,hB⟩ := hH
  have hxM : x ∈ M.atoms := hB.1 hx
  have he := Mole.full_degree_no_exit M hM hxM hd hex
  exact hp (hep ▸ he)

/-- A doubled pair with one absent neighbor at each atom is either absent
or exactly the two hyper-block joints. The statement uses only actual darts
and adjacency, and applies equally to old pairs and newly allocated rungs. -/
theorem hyperBlock_external_double_pair (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q : V} (hH : Mole.IsHyperBlock M A a b)
    (R : TwoIncidences M x y) (hne : x ≠ y) (hp : p ∉ A) (hq : q ∉ A)
    (hxp : M.Adj x p) (hyq : M.Adj y q) :
    (x ∉ A ∧ y ∉ A) ∨ (({x,y} : Finset V)={a,b} ∧ x ∈ A ∧ y ∈ A) := by
  have hmatch := hyperBlock_double_pair_membership M hM hH R
  by_cases hx : x ∈ A
  · have hy := hmatch.mp hx
    have hxj := hyperBlock_joint_of_external_neighbor M hM hH hx hp hxp
    have hyj := hyperBlock_joint_of_external_neighbor M hM hH hy hq hyq
    apply Or.inr
    refine ⟨?_,hx,hy⟩
    rcases hxj with rfl | rfl <;> rcases hyj with rfl | rfl
    · exact False.elim (hne rfl)
    · rfl
    · exact pair_comm _ _
    · exact False.elim (hne rfl)
  · exact Or.inl ⟨hx,fun hy => hx (hmatch.mpr hy)⟩

end WaveTurbulence.Vine
