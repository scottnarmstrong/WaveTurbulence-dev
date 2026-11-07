/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaComplement
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostBridgeCut
import Mathlib.Tactic

/-! # The actual virtual triple cut in the post-R beta good case -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A degree-three star partitioned into two nonempty actual targets has
one target receiving a unique actual star edge. -/
theorem exists_unique_first_edge_of_two_targets (M : Molecule V D) (v : V) (hv3 : M.deg v = 3)
    (A B : Finset V) (hdis : Disjoint A B)
    (hcover : ∀ p, M.atom p = v → M.atom (M.mate p) ∈ A ∨ M.atom (M.mate p) ∈ B)
    (hA : ∃ p, M.atom p = v ∧ M.atom (M.mate p) ∈ A)
    (hB : ∃ p, M.atom p = v ∧ M.atom (M.mate p) ∈ B) :
    (∃ p, M.atom p = v ∧ M.atom (M.mate p) ∈ A ∧
      ∀ q, M.atom q = v → M.atom (M.mate q) ∈ A → q = p) ∨
    (∃ p, M.atom p = v ∧ M.atom (M.mate p) ∈ B ∧
      ∀ q, M.atom q = v → M.atom (M.mate q) ∈ B → q = p) := by
  classical
  let X := (M.dartsAt v).filter (fun p => M.atom (M.mate p) ∈ A)
  let Y := (M.dartsAt v).filter (fun p => M.atom (M.mate p) ∈ B)
  have hXY : Disjoint X Y := by
    apply disjoint_left.mpr
    intro p hpX hpY
    exact disjoint_left.mp hdis (mem_filter.mp hpX).2 (mem_filter.mp hpY).2
  have hU : X ∪ Y = M.dartsAt v := by
    ext p
    simp only [X,Y,mem_union,mem_filter]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hp
      rcases hcover p ((Mole.mem_dartsAt M v p).mp hp) with h | h
      · exact Or.inl ⟨hp,h⟩
      · exact Or.inr ⟨hp,h⟩
  have hsum := card_union_of_disjoint hXY
  rw [hU] at hsum
  have hxpos : 0 < X.card := by
    obtain ⟨p,hp,hpA⟩ := hA
    exact card_pos.mpr ⟨p,mem_filter.mpr ⟨(Mole.mem_dartsAt M v p).mpr hp,hpA⟩⟩
  have hypos : 0 < Y.card := by
    obtain ⟨p,hp,hpB⟩ := hB
    exact card_pos.mpr ⟨p,mem_filter.mpr ⟨(Mole.mem_dartsAt M v p).mpr hp,hpB⟩⟩
  have hone : X.card = 1 ∨ Y.card = 1 := by
    change (M.dartsAt v).card = 3 at hv3
    omega
  rcases hone with hx | hy
  · left
    obtain ⟨p,hp⟩ := card_eq_one.mp hx
    have hpX : p ∈ X := by rw [hp]; simp
    have hh := mem_filter.mp hpX
    refine ⟨p,(Mole.mem_dartsAt M v p).mp hh.1,hh.2,?_⟩
    intro q hq hqA
    have hqX : q ∈ X := mem_filter.mpr ⟨(Mole.mem_dartsAt M v q).mpr hq,hqA⟩
    rw [hp] at hqX
    exact mem_singleton.mp hqX
  · right
    obtain ⟨p,hp⟩ := card_eq_one.mp hy
    have hpY : p ∈ Y := by rw [hp]; simp
    have hh := mem_filter.mp hpY
    refine ⟨p,(Mole.mem_dartsAt M v p).mp hh.1,hh.2,?_⟩
    intro q hq hqB
    have hqY : q ∈ Y := mem_filter.mpr ⟨(Mole.mem_dartsAt M v q).mpr hq,hqB⟩
    rw [hp] at hqY
    exact mem_singleton.mp hqY

/-- The actual two sides of a post-R beta split yield an OLD three-bond
cut: the selected mixed pair plus exactly one first-star edge. -/
theorem exists_old_virtual_triple_cut_of_post_mixed_sides (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ p, M.atom p ≠ M.atom (M.mate p))
    (hbridge : ∀ e, ¬ IsBridge M e) (hno : ¬ AdmitsBetaSplit M)
    (v : V) (hv3 : M.deg v = 3) (x y r s : RetainedDart M {v})
    (hy : M.atom y.val = M.atom x.val) (hr : M.atom r.val = M.atom x.val)
    (hs : M.atom s.val = M.atom x.val)
    (hfour : (eraseAtoms M {v}).deg (M.atom x.val) = 4)
    (hxo : M.out x.val = false) (hyo : M.out y.val = true)
    (hro : M.out r.val = false) (hso : M.out s.val = true)
    (U : Finset V) (hU : U ⊆ (eraseAtoms M {v}).atoms \ {M.atom x.val})
    (hcutU : boundaryDarts (eraseAtoms M {v}) U = {(eraseAtoms M {v}).mate x,(eraseAtoms M {v}).mate y})
    (hcutT : boundaryDarts (eraseAtoms M {v}) (((eraseAtoms M {v}).atoms \ {M.atom x.val}) \ U) =
      {(eraseAtoms M {v}).mate r,(eraseAtoms M {v}).mate s}) :
    (∃ p : D, M.atom p = v ∧ boundaryDarts M U = {M.mate x.val,M.mate y.val,M.mate p}) ∨
    (∃ p : D, M.atom p = v ∧ boundaryDarts M (((eraseAtoms M {v}).atoms \ {M.atom x.val}) \ U) =
      {M.mate r.val,M.mate s.val,M.mate p}) := by
  classical
  let N := eraseAtoms M {v}
  let T := (N.atoms \ {M.atom x.val}) \ U
  have hT : T ⊆ N.atoms \ {M.atom r.val} := by
    simpa only [hr] using (sdiff_subset : T ⊆ N.atoms \ {M.atom x.val})
  have hA := exists_first_edge_into_post_mixed_pair_side M hM hbridge hno v x y hy hfour hxo hyo U hU hcutU
  have hB := exists_first_edge_into_post_mixed_pair_side M hM hbridge hno v r s (hs.trans hr.symm)
    (by simpa only [hr] using hfour) hro hso T hT hcutT
  have hdis : Disjoint U T := disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp hb).2 ha)
  have hcover (p : D) (hp : M.atom p = v) : M.atom (M.mate p) ∈ U ∨ M.atom (M.mate p) ∈ T := by
    by_cases hpu : M.atom (M.mate p) ∈ U
    · exact Or.inl hpu
    · right
      have hpv : M.atom (M.mate p) ≠ v := fun h => hloop p (hp.trans h.symm)
      have hpb := first_edge_ne_surviving_four M hM v x hfour hp
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _,by simpa only [mem_singleton] using hpv⟩,
        by simpa only [mem_singleton] using hpb⟩,hpu⟩
  have hchoice := exists_unique_first_edge_of_two_targets M v hv3 U T hdis hcover hA hB
  rcases hchoice with ⟨p,hp,hpU,honly⟩ | ⟨p,hp,hpT,honly⟩
  · left
    have hb := boundary_old_eq_union_one_first_edge M v U
      (fun a ha => (mem_sdiff.mp (hU ha)).1) p hp hpU honly
    rw [hcutU,image_insert,image_singleton] at hb
    refine ⟨p,hp,?_⟩
    rw [hb]
    ext q
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  · right
    have hb := boundary_old_eq_union_one_first_edge M v T
      (fun a ha => (mem_sdiff.mp (hT ha)).1) p hp hpT honly
    rw [hcutT,image_insert,image_singleton] at hb
    refine ⟨p,hp,?_⟩
    rw [hb]
    ext q
    simp only [mem_union,mem_insert,mem_singleton]
    tauto

end WaveTurbulence.MoleProp
