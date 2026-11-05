/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineJointPairDegrees
import Mathlib.Tactic

/-! # A direct bond between VC joints forces one actual vine ingredient -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A direct endpoint bond in a VC excludes a nontrivial chain split:
the terminal joint has already used its whole degree within the last vine. -/
theorem VC_with_joint_adj_isSomeVine (M : Molecule V D) {U : Finset V} {a b : V}
    (hU : IsVC M U a b) (hab : M.Adj a b) : IsSomeVine M U a b := by
  obtain ⟨hB,n,hchain⟩ := hU
  cases hchain with
  | single h => exact h
  | @append S T a b c n hS hT hi _hne =>
    obtain ⟨X,hX⟩ := hT
    have haT := nested_block_joint_adj_mem M hX.1 hB subset_union_right hX.1.2.2.1
      (Or.inr rfl) hB.2.1 (Mole.adj_symmetric M hab)
    have haS := (chain_joints_mem hS).1
    have hmem : a ∈ S ∩ T := mem_inter.mpr ⟨haS,haT⟩
    rw [hi] at hmem
    exact False.elim (chain_joints_ne hS (mem_singleton.mp hmem))

/-- Degree one at a two-atom group comes from an actual bond between
its two atoms; it cannot be contributed by a self-loop. -/
theorem pair_degree_one_adj (M : Molecule V D) {a b : V} (hd : M.degIn {a,b} a=1) : M.Adj a b := by
  let T := (M.dartsAt a).filter (M.InGroup {a,b})
  have hc : T.card=1 := hd
  obtain ⟨d,hT⟩ := card_eq_one.mp hc
  have hdT : d ∈ T := by rw [hT]; exact mem_singleton_self _
  have hh := mem_filter.mp hdT
  have ha := (Mole.mem_dartsAt M a d).mp hh.1
  have hn : M.atom (M.mate d) ∈ ({a,b} : Finset V) := hh.2.2
  rcases mem_insert.mp hn with hloop | hbond
  · have hm : M.mate d ∈ T := by
      apply mem_filter.mpr
      refine ⟨(Mole.mem_dartsAt M a _).mpr hloop,?_,?_⟩
      · exact hloop.symm ▸ mem_insert_self _ _
      · rw [M.mate_mate,ha]
        exact mem_insert_self _ _
    rw [hT] at hm
    exact False.elim (M.mate_ne d (mem_singleton.mp hm))
  · exact ⟨d,ha,mem_singleton.mp hbond⟩

/-- The only VC whose joint-pair induced degree is one is a type V. -/
theorem VC_joint_pair_degree_one_isVineV (M : Molecule V D) {U : Finset V} {a b : V}
    (hU : IsVC M U a b) (hd : M.degIn {a,b} a=1) : M.IsVine .V U a b := by
  obtain ⟨X,hX⟩ := VC_with_joint_adj_isSomeVine M hU (pair_degree_one_adj M hd)
  have hs := (isVine_joint_pair_degrees hX).1
  rw [hd,template_sigma] at hs
  have he : X=.V := by
    cases X with
    | V => rfl
    | I => norm_num at hs
    | II => norm_num at hs
    | III => norm_num at hs
    | IV => norm_num at hs
    | VI => norm_num at hs
    | VII => norm_num at hs
    | VIII => norm_num at hs
  subst X
  exact hX

end WaveTurbulence.Vine
