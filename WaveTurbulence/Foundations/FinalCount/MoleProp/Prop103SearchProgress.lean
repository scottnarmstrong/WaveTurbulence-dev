/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaComponent
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaCore
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103OrdinaryStep
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
import Mathlib.Tactic

/-! # Actual finite-search progress for DH23 Proposition 10.3 -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The intrinsic graph conditions at the start of an ordinary search step.
Every field is a literal source graph condition; no count or future-step
witness is included. -/
structure SearchInput (M : Molecule V D) : Prop where
  molecule : M.IsMolecule
  loopless : ∀ z, M.atom z ≠ M.atom (M.mate z)
  simple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1
  nonempty : M.atoms.Nonempty
  connected : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  minDegree : ∀ a ∈ M.atoms, 3 ≤ M.deg a
  bridgeless : ∀ e, ¬ IsBridge M e
  noBeta : ¬ AdmitsBetaSplit M

/-- The actual configurations inspected after the first R operation. -/
def GoodAfterRemoval (M : Molecule V D) (v : V) : Prop :=
  (∃ a ∈ (eraseAtoms M {v}).atoms, OrdinaryDegreeGood (eraseAtoms M {v}) a) ∨
    AdmitsBetaSplit (eraseAtoms M {v})

/-- A source search input produces an actual good configuration or a
strictly smaller actual source search input obtained by R, B pruning, and
selection of a connected component. This is the well-founded progress
step, not an assumed good-removal schedule. -/
theorem actual_search_progress (M : Molecule V D) (hI : SearchInput M) :
    ∃ v ∈ M.atoms, M.deg v = 3 ∧
      (GoodAfterRemoval M v ∨ ∃ a ∈ (eraseAtoms M {v}).atoms,
        SearchInput (Mole.induced (bridgeCore (eraseAtoms M {v}))
          (componentSet (bridgeCore (eraseAtoms M {v})) a)) ∧
        (componentSet (bridgeCore (eraseAtoms M {v})) a).card < M.atoms.card) := by
  classical
  obtain ⟨z,hz⟩ := hI.nonempty
  obtain ⟨v,hv,_,hvne⟩ := hI.molecule.2 z hz
  have hv3 : M.deg v = 3 := by
    have hlo := hI.minDegree v hv
    have hhi := Mole.deg_le_four M hI.molecule hv
    omega
  refine ⟨v,hv,hv3,?_⟩
  let N := eraseAtoms M {v}
  by_cases hgood : ∃ a ∈ N.atoms, OrdinaryDegreeGood N a
  · exact Or.inl (Or.inl hgood)
  by_cases hbeta : AdmitsBetaSplit N
  · exact Or.inl (Or.inr hbeta)
  have hN : N.IsMolecule := isMolecule_eraseAtoms M hI.molecule {v}
  have hp := bridgeCore_profile_of_no_degree_good N
    (degree_profile_after_removing_three M hI.molecule hI.simple hI.minDegree v) hgood
  have hχ := circuitRank_ge_three_of_simple_min_degree M hI.loopless hI.simple hI.nonempty hI.minDegree hI.connected
  have hR := circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless hv hv3
  obtain ⟨a,ha,ha3⟩ := exists_degree_three_after_bridge_pruning N hN (by
    change 0 < (eraseAtoms M {v}).circuitRank
    omega) hp
  have haC : a ∈ componentSet (bridgeCore N) a :=
    (mem_componentSet _ _ _).mpr ⟨ha,Relation.EqvGen.refl a⟩
  right
  refine ⟨a,ha,?_,coreComponent_card_lt_after_removal M hv a⟩
  refine {
    molecule := induced_component_isMolecule _ (bridgeCore_isMolecule N hN) a
    loopless := fun z => hI.loopless z.val.val.val
    simple := induced_simple _ _ (bridgeCore_simple N (simple_eraseAtoms M {v} hI.simple))
    nonempty := ⟨a,haC⟩
    connected := selected_core_connected N a
    minDegree := ?_
    bridgeless := induced_component_bridgeless _ (bridgeCore_bridgefree_and_circuitRank N).1 a
    noBeta := ?_ }
  · intro b hb
    change 3 ≤ (Mole.induced (bridgeCore N) (componentSet (bridgeCore N) a)).deg b
    rcases selected_core_min_degree N hp ha3 b hb with h3 | h4
    · simpa only [h3] using (le_refl (3 : ℕ))
    · simpa only [h4] using (by decide : (3 : ℕ) ≤ 4)
  · intro hb
    have hcore := admitsBetaSplit_before_component_selection (bridgeCore N)
      (fun z => hI.loopless z.val.val) (bridgeCore_bridgefree_and_circuitRank N).1 a hb
    exact hbeta (admitsBetaSplit_before_bridgeCore N hN hcore)

end WaveTurbulence.MoleProp
