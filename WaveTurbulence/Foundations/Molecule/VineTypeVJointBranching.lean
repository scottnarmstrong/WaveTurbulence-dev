/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
public import WaveTurbulence.Foundations.Molecule.VineCoreJointEdges
import Mathlib.Tactic

/-! # Type-V joints have two distinct neighbors and cannot belong to a double bond -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A two-atom type-I piece cannot contain a degree-two atom with two
distinct neighbors in the containing group. Either joint order is allowed. -/
theorem typeI_not_contains_branching_atom (M : Molecule V D) {P S : Finset V}
    {x y v : V} (hI : M.IsVine .I P x y) (hPS : P ⊆ S) (hv : v ∈ P)
    (hd : M.degIn S v=2)
    (hb : ∃ u w,(Mole.induced M S).Adj v u ∧ (Mole.induced M S).Adj v w ∧ u ≠ w) : False := by
  obtain ⟨R⟩ := typeI_twoIncidences hI
  have hat := typeI_atoms hI
  rw [hat] at hv
  obtain ⟨u,w,hu,hw,hne⟩ := hb
  rcases mem_insert.mp hv with h | h
  · subst v
    have heu := twoIncidences_unique_internal_neighbor M R (hPS hI.1.2.1) (hPS hI.1.2.2.1) hd hu
    have hew := twoIncidences_unique_internal_neighbor M R (hPS hI.1.2.1) (hPS hI.1.2.2.1) hd hw
    exact hne (heu.trans hew.symm)
  · have he := mem_singleton.mp h
    subst v
    have heu := twoIncidences_unique_internal_neighbor M R.mates (hPS hI.1.2.2.1) (hPS hI.1.2.1) hd hu
    have hew := twoIncidences_unique_internal_neighbor M R.mates (hPS hI.1.2.2.1) (hPS hI.1.2.1) hd hw
    exact hne (heu.trans hew.symm)

/-- Each joint of an actual type V has two distinct internal neighbors. -/
theorem typeV_joint_branching {M : Molecule V D} {S : Finset V} {a b v : V}
    (hV : M.IsVine .V S a b) (hv : v=a ∨ v=b) :
    ∃ u w,(Mole.induced M S).Adj v u ∧ (Mole.induced M S).Adj v w ∧ u ≠ w := by
  obtain ⟨hB,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hvS : v ∈ S := hv.elim (fun h => h.symm ▸ hB.2.1) (fun h => h.symm ▸ hB.2.2.1)
  have hlow : R.f v<2 := (realization_index_lt_two_iff R hB hvS).mpr hv
  have hlabel : R.f v=0 ∨ R.f v=1 := by omega
  have toCore (i : Fin 9) (hi : R.f v=i.1) : v=(R.coreAtom i).1 :=
    R.injOn hvS (R.coreAtom i).2 (hi.trans (R.label_coreAtom i).symm)
  have induced {i j : Fin 9} (ha : M.Adj (R.coreAtom i).1 (R.coreAtom j).1) :
      (Mole.induced M S).Adj (R.coreAtom i).1 (R.coreAtom j).1 :=
    (Mole.induced_adj_iff M S _ _).mpr ⟨ha,(R.coreAtom i).2,(R.coreAtom j).2⟩
  rcases hlabel with h0 | h1
  · have he := toCore (0 : Fin 9) h0
    subst v
    exact ⟨(R.coreAtom (1 : Fin 9)).1,(R.coreAtom (2 : Fin 9)).1,
      induced (R.core_joint_adj (0 : Fin 9) (1 : Fin 9) (by decide) (by decide)),
      induced (R.core_joint_adj (0 : Fin 9) (2 : Fin 9) (by decide) (by decide)),
      fun h => (by decide : (1 : Fin 9) ≠ 2) (R.coreAtom_injective h)⟩
  · have he := toCore (1 : Fin 9) h1
    subst v
    exact ⟨(R.coreAtom (0 : Fin 9)).1,(R.coreAtom (3 : Fin 9)).1,
      induced (Mole.adj_symmetric M (R.core_joint_adj (0 : Fin 9) (1 : Fin 9) (by decide) (by decide))),
      induced (R.core_joint_adj (1 : Fin 9) (3 : Fin 9) (by decide) (by decide)),
      fun h => (by decide : (0 : Fin 9) ≠ 3) (R.coreAtom_injective h)⟩

/-- A contained double bond avoids both joints of a type-V branch. -/
theorem typeI_in_typeV_joints_absent (M : Molecule V D) {P S : Finset V} {x y a b : V}
    (hI : M.IsVine .I P x y) (hV : M.IsVine .V S a b) (hPS : P ⊆ S) : a ∉ P ∧ b ∉ P := by
  have hd := Mole.block_joint_degrees M hV.1
  exact ⟨fun ha => typeI_not_contains_branching_atom M hI hPS ha hd.1 (typeV_joint_branching hV (Or.inl rfl)),
    fun hb => typeI_not_contains_branching_atom M hI hPS hb hd.2 (typeV_joint_branching hV (Or.inr rfl))⟩

end WaveTurbulence.Vine
