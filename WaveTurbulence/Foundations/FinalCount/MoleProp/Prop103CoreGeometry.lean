/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeCore
public import WaveTurbulence.Foundations.FinalCount.Degen.EraseMolecule
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Actual local geometry of bridge pruning in the good-step search -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Bridge pruning only decreases each oriented degree. -/
theorem card_filtered_dartsAt_bridgeCore_le (M : Molecule V D) (z : V)
    (p : D → Prop) [DecidablePred p] :
    (((bridgeCore M).dartsAt z).filter (fun x => p x.val)).card ≤
      ((M.dartsAt z).filter p).card := by
  classical
  have hs : ((((bridgeCore M).dartsAt z).filter (fun x => p x.val)).image
      (fun x => x.val)) ⊆ (M.dartsAt z).filter p := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨ha,hp⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M z a.val).mpr ((mem_filter.mp ha).2),hp⟩
  have hc := card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

/-- A degree-four vertex of the core retained every old dart. -/
theorem adj_bridgeCore_of_four (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (ha : a ∈ M.atoms) (hfour : (bridgeCore M).deg a = 4)
    (hab : M.Adj a b) : (bridgeCore M).Adj a b := by
  classical
  obtain ⟨x,hxa,hxb⟩ := hab
  have he := degree_bridgeCore_add_incident_bridges M a
  have hcap := Mole.deg_le_four M hM ha
  have hempty : ((M.dartsAt a).filter (fun x => IsBridge M x)) = ∅ :=
    card_eq_zero.mp (by omega)
  have hnb : ¬ IsBridge M x := by
    intro hx
    have hh : x ∈ (M.dartsAt a).filter (fun x => IsBridge M x) :=
      mem_filter.mpr ⟨(Mole.mem_dartsAt M a x).mpr hxa,hx⟩
    rw [hempty] at hh
    simpa using hh
  exact ⟨⟨x,hnb⟩,hxa,hxb⟩

/-- Source B operations preserve the molecule axioms, including nonsaturation
of each actual connected component. -/
theorem bridgeCore_isMolecule (M : Molecule V D) (hM : M.IsMolecule) :
    (bridgeCore M).IsMolecule := by
  classical
  constructor
  · intro z hz
    exact ⟨(card_filtered_dartsAt_bridgeCore_le M z (fun x => M.out x = true)).trans
        (hM.1 z hz).1,
      (card_filtered_dartsAt_bridgeCore_le M z (fun x => M.out x = false)).trans
        (hM.1 z hz).2⟩
  · intro z hz
    by_contra hn
    have hsat (a : V) (ha : a ∈ M.atoms)
        (hza : (bridgeCore M).SameComponent z a) : (bridgeCore M).deg a = 4 := by
      by_contra hne
      exact hn ⟨a,ha,hza,hne⟩
    let C := fun a => a ∈ M.atoms ∧ (bridgeCore M).SameComponent z a
    have hclosed (a b : V) (hab : M.Adj a b) (ha : C a) : C b := by
      have hab' := adj_bridgeCore_of_four M hM ha.1 (hsat a ha.1 ha.2) hab
      obtain ⟨x,hxa,hxb⟩ := hab
      exact ⟨hxb ▸ M.atom_mem (M.mate x),
        Relation.EqvGen.trans _ _ _ ha.2 (Relation.EqvGen.rel _ _ hab')⟩
    have hpath (a b : V) (hab : M.SameComponent a b) : C a ↔ C b := by
      induction hab with
      | rel a b h => exact ⟨hclosed a b h,hclosed b a (Mole.adj_symmetric M h)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    obtain ⟨u,hu,hzu,hu4⟩ := hM.2 z hz
    have huC := (hpath z u hzu).mp ⟨hz,Relation.EqvGen.refl z⟩
    have he := degree_bridgeCore_add_incident_bridges M u
    have hfour := hsat u huC.1 huC.2
    have hcap := Mole.deg_le_four M hM hu
    apply hu4
    omega

/-- A degree-one vertex produces a genuine bridge, without a looplessness
premise: its unique dart cannot have its mate at the same vertex. -/
theorem exists_bridge_of_degree_one (M : Molecule V D) {a : V} (ha : M.deg a = 1) :
    ∃ e : D, IsBridge M e := by
  classical
  obtain ⟨e,he⟩ := card_eq_one.mp ha
  have hea : M.atom e = a := (Mole.mem_dartsAt M a e).mp (by rw [he]; simp)
  have hma : M.atom (M.mate e) ≠ a := by
    intro h
    have hm : M.mate e ∈ M.dartsAt a := (Mole.mem_dartsAt M a _).mpr h
    rw [he] at hm
    exact M.mate_ne e (mem_singleton.mp hm)
  refine ⟨e,isBridge_of_single_boundary M {a} ?_⟩
  ext x
  simp only [boundaryDarts,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro hx
    have hh : x ∈ M.dartsAt a := (Mole.mem_dartsAt M a x).mpr hx.1
    rw [he] at hh
    exact mem_singleton.mp hh
  · rintro rfl
    exact ⟨hea,hma⟩

/-- Every actual vertex of a bridge-free graph avoids degree one. -/
theorem degree_ne_one_of_bridgeless (M : Molecule V D)
    (hbridge : ∀ e, ¬ IsBridge M e) (a : V) : M.deg a ≠ 1 := by
  intro h
  obtain ⟨e,he⟩ := exists_bridge_of_degree_one M h
  exact hbridge e he

/-- The local exhaustion behind the source's ordinary R/B step.  Its
hypotheses exclude exactly the degree-two/zero-bridge, degree-three/one-bridge,
and degree-four/two-bridge configurations; the conclusion is an actual core
vertex degree, rather than an assumed next-state invariant. -/
theorem bridgeCore_degree_profile (M : Molecule V D) (a : V)
    [DecidablePred (IsBridge M)]
    (hlo : 2 ≤ M.deg a) (hhi : M.deg a ≤ 4)
    (h2 : M.deg a = 2 → ((M.dartsAt a).filter (IsBridge M)).card ≠ 0)
    (h3 : M.deg a = 3 → ((M.dartsAt a).filter (IsBridge M)).card ≠ 1)
    (h4 : M.deg a = 4 → ((M.dartsAt a).filter (IsBridge M)).card ≠ 2) :
    (bridgeCore M).deg a = 0 ∨ (bridgeCore M).deg a = 3 ∨
      (bridgeCore M).deg a = 4 := by
  have he := degree_bridgeCore_add_incident_bridges M a
  change (bridgeCore M).deg a + ((M.dartsAt a).filter (IsBridge M)).card = M.deg a at he
  have hn := degree_ne_one_of_bridgeless (bridgeCore M)
    (bridgeCore_bridgefree_and_circuitRank M).1 a
  by_cases hh2 : M.deg a = 2
  · have hh := h2 hh2
    omega
  by_cases hh3 : M.deg a = 3
  · have hh := h3 hh3
    omega
  have hh4 : M.deg a = 4 := by omega
  have hh := h4 hh4
  omega

/-- An isolated vertex has no other vertex in its actual component. -/
theorem sameComponent_eq_of_degree_zero (M : Molecule V D) {a b : V}
    (ha : M.deg a = 0) (hab : M.SameComponent a b) : b = a := by
  have hz : M.dartsAt a = ∅ := card_eq_zero.mp ha
  have hadj (x y : V) (hxy : M.Adj x y) : x = a ↔ y = a := by
    constructor
    · intro hxa
      obtain ⟨e,he,_⟩ := hxy
      rw [hxa] at he
      have hh := (Mole.mem_dartsAt M a e).mpr he
      rw [hz] at hh
      exact False.elim (by simpa using hh)
    · intro hya
      obtain ⟨e,_,he⟩ := hxy
      rw [hya] at he
      have hh := (Mole.mem_dartsAt M a (M.mate e)).mpr he
      rw [hz] at hh
      exact False.elim (by simpa using hh)
  have hpath (x y : V) (hxy : M.SameComponent x y) : x = a ↔ y = a := by
    induction hxy with
    | rel x y h => exact hadj x y h
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (hpath a b hab).mp rfl

/-- Nonsaturation supplies a degree-three atom in every nonisolated core
component once the actual local degree exhaustion has been established. -/
theorem exists_degree_three_in_core_component (M : Molecule V D) (hM : M.IsMolecule)
    (hp : ∀ a ∈ M.atoms, (bridgeCore M).deg a = 0 ∨
      (bridgeCore M).deg a = 3 ∨ (bridgeCore M).deg a = 4)
    {v : V} (hv : v ∈ M.atoms) (hpos : 0 < (bridgeCore M).deg v) :
    ∃ a ∈ M.atoms, (bridgeCore M).SameComponent v a ∧ (bridgeCore M).deg a = 3 := by
  obtain ⟨a,ha,hva,hne⟩ := (bridgeCore_isMolecule M hM).2 v hv
  refine ⟨a,ha,hva,?_⟩
  rcases hp a ha with hz | h3 | h4
  · have hvEq := sameComponent_eq_of_degree_zero (bridgeCore M) hz
      (Relation.EqvGen.symm _ _ hva)
    rw [hvEq,hz] at hpos
    omega
  · exact h3
  · exact False.elim (hne h4)

/-- An old bridge cannot have both endpoints inside a single actual core
component.  A core path is already an old path avoiding that bond. -/
theorem not_isBridge_of_core_component_internal (M : Molecule V D) (v : V) (x : D)
    (hx : M.InGroup (componentSet (bridgeCore M) v) x) : ¬ IsBridge M x := by
  have hp : (bridgeCore M).SameComponent (M.atom x) (M.atom (M.mate x)) :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ ((mem_componentSet _ _ _).mp hx.1).2)
      ((mem_componentSet _ _ _).mp hx.2).2
  intro hb
  apply hb
  apply Relation.EqvGen.mono (fun a b hab => ?_) _ _ hp
  obtain ⟨e,hea,heb⟩ := hab
  refine ⟨e.val,hea,heb,?_,?_⟩
  · intro he
    exact e.property (he.symm ▸ hb)
  · intro he
    exact e.property (he.symm ▸ (isBridge_mate_iff M x).mpr hb)

/-- Selecting one component after the source B operations yields an actual
induced subgraph of the old graph, with no missing internal bond. -/
noncomputable def coreComponentDartEquiv (M : Molecule V D) (v : V) :
    {x : NonBridgeDart M // (bridgeCore M).InGroup (componentSet (bridgeCore M) v) x} ≃
      {x : D // M.InGroup (componentSet (bridgeCore M) v) x} := by
  classical
  exact {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,not_isBridge_of_core_component_internal M v x.val x.property⟩,x.property⟩
    left_inv := fun x => Subtype.ext (Subtype.ext rfl)
    right_inv := fun x => Subtype.ext rfl }

/-- The selected component's circuit rank is exactly that of the literal old
induced subgraph, so subsequent neutral discarding can target old atoms. -/
theorem circuitRank_core_component_eq_induced (M : Molecule V D) (v : V) :
    (Mole.induced (bridgeCore M) (componentSet (bridgeCore M) v)).circuitRank =
      (Mole.induced M (componentSet (bridgeCore M) v)).circuitRank := by
  classical
  exact circuitRank_eq_of_dart_equiv _ _ (coreComponentDartEquiv M v) rfl
    (fun _ => rfl) (fun _ => Subtype.ext rfl) (fun _ => rfl)

/-- Positive circuit rank forces a nonisolated atom. -/
theorem exists_positive_degree_of_circuitRank_pos (M : Molecule V D)
    (hχ : 0 < M.circuitRank) : ∃ v ∈ M.atoms, 0 < M.deg v := by
  have hc := Mole.numComponents_le_card_atoms M
  have hb : 0 < M.bonds.card := by
    unfold Molecule.circuitRank at hχ
    omega
  obtain ⟨e,he⟩ := card_pos.mp hb
  refine ⟨M.atom e,M.atom_mem e,card_pos.mpr ?_⟩
  exact ⟨e,(Mole.mem_dartsAt M _ e).mpr rfl⟩

/-- Ordinary pruning cannot exhaust a graph of positive circuit rank into
isolates.  This produces an actual next degree-three vertex, rather than
assuming a nontrivial surviving search component. -/
theorem exists_degree_three_after_bridge_pruning (M : Molecule V D)
    (hM : M.IsMolecule) (hχ : 0 < M.circuitRank)
    (hp : ∀ a ∈ M.atoms, (bridgeCore M).deg a = 0 ∨
      (bridgeCore M).deg a = 3 ∨ (bridgeCore M).deg a = 4) :
    ∃ a ∈ M.atoms, (bridgeCore M).deg a = 3 := by
  have hχ' : 0 < (bridgeCore M).circuitRank := by
    rw [(bridgeCore_bridgefree_and_circuitRank M).2]
    exact hχ
  obtain ⟨v,hv,hvpos⟩ := exists_positive_degree_of_circuitRank_pos (bridgeCore M) hχ'
  obtain ⟨a,ha,_,h3⟩ := exists_degree_three_in_core_component M hM hp hv hvpos
  exact ⟨a,ha,h3⟩

end WaveTurbulence.MoleProp
