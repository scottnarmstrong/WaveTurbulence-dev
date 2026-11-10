/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Spine.MoleculeReorderJoints
import Mathlib.Tactic
/-! # Per-vine facts of `𝒱_γ` used by the Stage 1 construction (packet L5a, item C)

Main's Stage 1 combinatorics uses only a handful of facts about a single vine of the family; everything else is about
blocks and chains. This module proves them for `𝒱_γ` (L6's `Src.IsSomeVine γ`, i.e. `Molecule.IsVineGamma γ`):
- `isSomeVine_connected`: a member is connected (it is a block);
- `isSomeVine_typeI_of_card_lt_four`: a member with fewer than four atoms is a double bond (I) (main:
  `Vine.isVine_typeI_of_card_lt_four`; a T-vine has at least five atoms, `tvine_card_ge_five`);
- `isSomeVine_erase_connected`: a member stays connected after removing any one atom (main:
  `Vine.isVine_erase_connected`); for a T-vine this is N2 Theorem 1.15 (F1) (named input `TVineF1Input`) plus the
  joint case (`tvine_erase_joint_connected`: a joint has a neighbour in the interior since `σ < 2`);
- `isSomeVine_interior_connected`: the interior is connected (main: `Vine.isVine_interior_connected`; (F1));
- `isSomeVine_rejoint`: the joints of a member are those of any block structure on its atoms.
For γ > 1/2 (drawn vines) and the bad vines (I), (II) main's lemmas are used verbatim. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Connectivity through the bonds of `S` gives connectivity of the induced group (main's `Vine.GroupConnected`). -/
theorem vineConn_of_molConn {M : Molecule V D} {S : Finset V} (h : M.GroupConnected S) :
    Vine.GroupConnected M S := by
  intro u hu v hv
  have key : ∀ p q, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧
      M.atom (M.mate x) = b) p q → p = q ∨ (p ∈ S ∧ q ∈ S ∧ (Mole.induced M S).SameComponent p q) := by
    intro p q h
    induction h with
    | rel a b hab =>
      obtain ⟨x, hx, rfl, rfl⟩ := hab
      exact Or.inr ⟨hx.1, hx.2, Relation.EqvGen.rel _ _
        ((Mole.induced_adj_iff M S _ _).mpr ⟨⟨x, rfl, rfl⟩, hx.1, hx.2⟩)⟩
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | ⟨h1, h2, h3⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1, Relation.EqvGen.symm _ _ h3⟩
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨h1, h2, h3⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨h4, h5, h6⟩
        · exact Or.inr ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h5, Relation.EqvGen.trans _ _ _ h3 h6⟩
  rcases key u v (h u hu v hv) with rfl | ⟨_, _, h⟩
  · exact Relation.EqvGen.refl _
  · exact h

/-- A block is connected (induced form). -/
theorem block_vineConn {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    Vine.GroupConnected M S :=
  vineConn_of_molConn hB.2.2.2.2.2.2.2.2.2

/-- Every member of `𝒱_γ` is connected. -/
theorem isSomeVine_connected {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine γ M S a b) : Vine.GroupConnected M S :=
  block_vineConn (Src.isBlock_of_isSomeVine h)

/-! ## Size -/

/-! ## Connectivity after removing one atom -/

/-- The named input `TVineF1Input`, carried as an instance (`Fact`) so that it propagates to the lemmas that use it. -/
theorem tvineF1 [h : Fact TVineF1Input] : TVineF1Input := h.out

/-- A joint of a T-vine has a neighbour (through a bond of the group) in the interior: `σ < 2` and the joint has two
incidences in the group, no loop. -/
theorem tvine_joint_interior_neighbor {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (h : M.IsTVine S j₁ j₂) :
    ∃ z ∈ S, z ≠ j₁ ∧ z ≠ j₂ ∧ M.Adj j₁ z := by
  classical
  obtain ⟨hB, -, G, -, ⟨hσ, -⟩, -⟩ := h
  have hj := hB.2.1
  have hj2 := hB.2.2.1
  have hne := hB.2.2.2.1
  have hd := (Mole.block_joint_degrees M hB).1
  have hloop := Vine.connected_degree_two_no_loop M (block_vineConn hB) hj hj2 hne hd
  have hno : ∀ x, M.atom x = j₁ → M.atom (M.mate x) ≠ j₁ := fun x hx he => hloop ⟨x, hx, he⟩
  have hp := Mole.degIn_pair_eq_bondsBetween M hne hno
  have hs : M.sigma j₁ j₂ = M.bondsBetween j₁ j₂ := rfl
  have hlt : M.degIn {j₁, j₂} j₁ < M.degIn S j₁ := by omega
  have hex : ∃ x ∈ (M.dartsAt j₁).filter (M.InGroup S),
      x ∉ (M.dartsAt j₁).filter (M.InGroup {j₁, j₂}) := by
    by_contra hc
    push Not at hc
    have hcard := Finset.card_le_card (show (M.dartsAt j₁).filter (M.InGroup S) ⊆
      (M.dartsAt j₁).filter (M.InGroup {j₁, j₂}) from hc)
    change M.degIn S j₁ ≤ M.degIn {j₁, j₂} j₁ at hcard
    omega
  obtain ⟨x, hx, hxnot⟩ := hex
  obtain ⟨hxv, hxa, hxm⟩ := Finset.mem_filter.mp hx
  have hax := (Mole.mem_dartsAt M j₁ x).mp hxv
  have hnot : M.atom (M.mate x) ≠ j₁ ∧ M.atom (M.mate x) ≠ j₂ := by
    constructor <;> intro he <;> apply hxnot <;> apply Finset.mem_filter.mpr
    · exact ⟨hxv, by simp [Molecule.InGroup, hax, he]⟩
    · exact ⟨hxv, by simp [Molecule.InGroup, hax, he]⟩
  exact ⟨M.atom (M.mate x), hxm, hnot.1, hnot.2, ⟨x, hax, rfl⟩⟩

/-- A T-vine stays connected after removing its second joint ((F1) and the joint neighbour). -/
theorem tvine_erase_joint_connected [Fact TVineF1Input] {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (h : M.IsTVine S j₁ j₂) :
    Vine.GroupConnected M (S.erase j₂) := by
  obtain ⟨z, hzS, hz1, hz2, hadj⟩ := tvine_joint_interior_neighbor h
  have hI : Vine.GroupConnected M ((S.erase j₁).erase j₂) := by
    rw [show (S.erase j₁).erase j₂ = (S.erase j₂).erase j₁ from Finset.erase_right_comm]
    exact vineConn_of_molConn (tvineF1 M S j₂ j₁ (isTVine_swap h)).1
  have hsub : (S.erase j₁).erase j₂ ⊆ S.erase j₂ := by
    intro v hv
    exact mem_erase.mpr ⟨(mem_erase.mp hv).1, (mem_erase.mp (mem_erase.mp hv).2).2⟩
  have hzI : z ∈ (S.erase j₁).erase j₂ := mem_erase.mpr ⟨hz2, mem_erase.mpr ⟨hz1, hzS⟩⟩
  have hB := h.1
  have hj1 : j₁ ∈ S.erase j₂ := mem_erase.mpr ⟨hB.2.2.2.1, hB.2.1⟩
  have toZ : ∀ u ∈ S.erase j₂, (Mole.induced M (S.erase j₂)).SameComponent u z := by
    intro u hu
    by_cases hu1 : u = j₁
    · subst hu1
      exact Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M _ _ _).mpr ⟨hadj, hj1, hsub hzI⟩)
    · have huI : u ∈ (S.erase j₁).erase j₂ :=
        mem_erase.mpr ⟨(mem_erase.mp hu).1, mem_erase.mpr ⟨hu1, (mem_erase.mp hu).2⟩⟩
      exact Vine.induced_path_mono M hsub (hI u huI z hzI)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (toZ u hu) (Relation.EqvGen.symm _ _ (toZ v hv))

/-- A T-vine stays connected after removing any one atom (N2 Theorem 1.15 (F1) plus the joint case). -/
theorem tvine_erase_connected [Fact TVineF1Input] {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) (z : V) :
    Vine.GroupConnected M (S.erase z) := by
  by_cases hz : z ∈ S
  · by_cases hza : z = a
    · subst hza; exact tvine_erase_joint_connected (isTVine_swap h)
    · by_cases hzb : z = b
      · subst hzb; exact tvine_erase_joint_connected h
      · exact vineConn_of_molConn ((tvineF1 M S a b h).2 z hz hza hzb)
  · rw [Finset.erase_eq_self.mpr hz]
    exact block_vineConn h.1

/-- **Every member of `𝒱_γ` stays connected after removing any one atom** (main's `Vine.isVine_erase_connected`). -/
theorem isSomeVine_erase_connected [Fact TVineF1Input] {γ : ℝ} {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) (z : V) :
    Vine.GroupConnected M (S.erase z) := by
  rcases h with ⟨-, h | h | h⟩ | ⟨-, X, h⟩
  · exact Vine.isVine_erase_connected h z
  · exact Vine.isVine_erase_connected h z
  · exact tvine_erase_connected h z
  · exact Vine.isVine_erase_connected h z

end WaveTurbulence.GammaLow.Fama
