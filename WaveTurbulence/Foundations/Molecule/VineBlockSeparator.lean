/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
import Mathlib.Tactic

/-! # A nested terminal block cannot cross its shared joint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- At a connected degree-two atom, a loop would consume both available
darts and isolate it from every other atom of the group. -/
theorem connected_degree_two_no_loop (M : Molecule V D) {S : Finset V}
    (hconn : GroupConnected M S) {b c : V} (hb : b ∈ S) (hc : c ∈ S)
    (hbc : b ≠ c) (hd : M.degIn S b=2) : ¬M.Adj b b := by
  classical
  rintro ⟨d,hdb,hdmb⟩
  let F := (M.dartsAt b).filter (M.InGroup S)
  have hdF : d ∈ F := mem_filter.mpr ⟨(Mole.mem_dartsAt M b d).mpr hdb,hdb.symm ▸ hb,hdmb.symm ▸ hb⟩
  have hmF : M.mate d ∈ F := mem_filter.mpr ⟨(Mole.mem_dartsAt M b _).mpr hdmb,
    hdmb.symm ▸ hb,by rw [M.mate_mate]; exact hdb.symm ▸ hb⟩
  have hpair : ({d,M.mate d} : Finset D)=F := by
    apply eq_of_subset_of_card_le
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · exact hdF
      · exact mem_singleton.mp he ▸ hmF
    · rw [card_pair (M.mate_ne d).symm]
      exact hd.le
  have hclosed (v : V) (hadj : (Mole.induced M S).Adj b v) : v=b := by
    obtain ⟨⟨e,heb,hev⟩,_hbS,hvS⟩ := (Mole.induced_adj_iff M S b v).mp hadj
    have heF : e ∈ F := mem_filter.mpr ⟨(Mole.mem_dartsAt M b e).mpr heb,heb.symm ▸ hb,hev.symm ▸ hvS⟩
    rw [← hpair] at heF
    rcases mem_insert.mp heF with rfl | heF
    · exact hev.symm.trans hdmb
    · have he := mem_singleton.mp heF
      subst e
      rw [M.mate_mate] at hev
      exact hev.symm.trans hdb
  have inv {u v : V} (hp : (Mole.induced M S).SameComponent u v) : (u=b ↔ v=b) := by
    induction hp with
    | rel u v huv =>
      constructor
      · intro he
        subst u
        exact hclosed v huv
      · intro he
        subst v
        exact hclosed u (Mole.adj_symmetric _ huv)
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  exact hbc ((inv (hconn b hb c hc)).mp rfl).symm

/-- A terminal nested block is closed within its ambient block away from
the shared joint. At the other joint, equality of the two restricted degrees
identifies the actual darts; at interior atoms all four incidences are internal. -/
theorem terminal_block_adj_mem (M : Molecule V D) (hM : M.IsMolecule)
    {T U : Finset V} {a b c u v : V} (hT : M.IsBlock T b c) (hU : M.IsBlock U a c)
    (hTU : T ⊆ U) (hv : v ∈ T) (hvb : v ≠ b) (hu : u ∈ U) (hadj : M.Adj v u) : u ∈ T := by
  by_cases hvc : v=c
  · subst v
    have he := internal_darts_eq_of_nested_degree M hTU c
      ((Mole.block_joint_degrees M hT).2.trans (Mole.block_joint_degrees M hU).2.symm)
    obtain ⟨d,hdc,hdu⟩ := hadj
    have hdU : d ∈ (M.dartsAt c).filter (M.InGroup U) := mem_filter.mpr
      ⟨(Mole.mem_dartsAt M c d).mpr hdc,hdc.symm ▸ hTU hv,hdu.symm ▸ hu⟩
    rw [← he] at hdU
    exact hdu ▸ (mem_filter.mp hdU).2.2
  · exact Mole.block_interior_adj_mem M hM hT hv hvb hvc hadj

end WaveTurbulence.Vine
