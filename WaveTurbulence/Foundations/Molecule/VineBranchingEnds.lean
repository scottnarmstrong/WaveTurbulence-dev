/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeIIncidences
public import WaveTurbulence.Foundations.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.Molecule.VineClosedDoubleBlock
public import WaveTurbulence.Foundations.Molecule.VineEraseChainIngredient
import Mathlib.Tactic

/-! # Short chains with branching endpoints are single vines -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An endpoint with two distinct internal neighbors cannot carry an
end ingredient of type I. -/
theorem no_typeI_at_branching_joint (M : Molecule V D) {S : Finset V} {a x : V}
    (ha : a ∈ S) (hd : M.degIn S a=2)
    (hbranch : ∃ u v,(Mole.induced M S).Adj a u ∧
      (Mole.induced M S).Adj a v ∧ u ≠ v)
    {A : Finset V} (hI : M.IsVine .I A a x) (hAS : A ⊆ S) : False := by
  obtain ⟨R⟩ := typeI_twoIncidences hI
  obtain ⟨u,v,hu,hv,hne⟩ := hbranch
  have hx : x ∈ S := hAS hI.1.2.2.1
  have heu := twoIncidences_unique_internal_neighbor M R ha hx hd hu
  have hev := twoIncidences_unique_internal_neighbor M R ha hx hd hv
  exact hne (heu.trans hev.symm)

omit [DecidableEq D] in
/-- A chain with one ingredient is a vine. -/
theorem chain_one_isSomeVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Chain M S a b 1) : IsSomeVine M S a b := by
  cases h with
  | single h => exact h
  | append h _ _ _ => have := chain_pos h; omega

/-- Every chain on fewer than seven atoms with two distinct neighbors at
each joint is a single vine. This excludes the short side pieces of the
finite cores from being multi-ingredient chains. -/
theorem small_chain_single_of_branching_ends (M : Molecule V D)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {n : ℕ} (h : Chain M S a b n)
    (hcard : S.card<7)
    (ha : ∃ u v,(Mole.induced M S).Adj a u ∧ (Mole.induced M S).Adj a v ∧ u ≠ v)
    (hb : ∃ u v,(Mole.induced M S).Adj b u ∧ (Mole.induced M S).Adj b v ∧ u ≠ v) :
    IsSomeVine M S a b := by
  have hd := Mole.block_joint_degrees M hB
  rcases chain_small_end_typeI h hcard with hn | ⟨A,x,hI,hAS⟩ | ⟨A,x,hI,hAS⟩
  · subst n
    exact chain_one_isSomeVine h
  · exact False.elim (no_typeI_at_branching_joint M hB.2.1 hd.1 ha hI hAS)
  · obtain ⟨R⟩ := typeI_twoIncidences hI
    obtain ⟨u,v,hu,hv,hne⟩ := hb
    have hx := hAS hI.1.2.1
    have heu := twoIncidences_unique_internal_neighbor M R.mates hB.2.2.1 hx hd.2 hu
    have hev := twoIncidences_unique_internal_neighbor M R.mates hB.2.2.1 hx hd.2 hv
    exact False.elim (hne (heu.trans hev.symm))

omit [DecidableEq D] in
/-- No individual vine has five atoms, including the F72 Q-block family. -/
theorem not_isVine_card_five {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (hc : S.card=5) : ¬M.IsVine X S a b := by
  intro h
  obtain ⟨k,hk,hs,_hb⟩ := isVine_counts h
  cases X <;> norm_num [VineType.template] at hs hk <;> omega

/-- A five-atom block with branching joints is not a VC. Seven atoms
are deliberately excluded: two four-atom Q-blocks can form such a chain. -/
theorem not_isVC_five_of_branching (M : Molecule V D)
    {S : Finset V} {a b : V} (hcard : S.card=5)
    (ha : ∃ u v,(Mole.induced M S).Adj a u ∧ (Mole.induced M S).Adj a v ∧ u ≠ v)
    (hb : ∃ u v,(Mole.induced M S).Adj b u ∧ (Mole.induced M S).Adj b v ∧ u ≠ v) :
    ¬IsVC M S a b := by
  rintro ⟨hB,n,hC⟩
  obtain ⟨X,hX⟩ := small_chain_single_of_branching_ends M hB hC (by omega) ha hb
  exact not_isVine_card_five hcard hX

omit [DecidableEq D] in
/-- A five/seven-atom group remaining connected after every one-atom
removal cannot be a VC. This excludes the actual short triangular sides
without excluding the seven-atom concatenation of two Q-blocks (F72). -/
theorem not_isVC_five_or_seven_of_erase_connected (M : Molecule V D)
    (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hcard : S.card=5 ∨ S.card=7) (hconn : ∀ z,GroupConnected M (S.erase z)) :
    ¬IsVC M S a b := by
  rintro ⟨hB,n,hC⟩
  obtain ⟨T,p,q,hT,hST⟩ := erase_connected_in_chain_ingredient M hM hconn hC hB
    (Finset.Subset.refl S)
  obtain ⟨_hC,⟨X,hX⟩,hTS⟩ := chainIngredient_spec hT
  have heq : T=S := Finset.Subset.antisymm hTS hST
  subst T
  rcases hcard with h5 | h7
  · exact not_isVine_card_five h5 hX
  · exact not_isVine_card_seven h7 hX

end WaveTurbulence.Vine
