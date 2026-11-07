/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodSelectorSupport
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostDegreeCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103IncidentBridgeRemoval
import Mathlib.Tactic

/-! # Actual cubic one-bridge good configurations, including repeated labels -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual post-degree-three/one-bridge case chooses all stars and
OLD cuts internally, retaining both affine cut orientations and the
repeated-shared positive branch. -/
theorem select_good_post_degree_three (M : Molecule V D) (hI : SearchInput M)
    {a b : V} (ha : a ∈ M.atoms) (ha3 : M.deg a = 3)
    (hb : b ∈ (eraseAtoms M {a}).atoms) (hb3 : (eraseAtoms M {a}).deg b = 3)
    [DecidablePred (IsBridge (eraseAtoms M {a}))]
    (hcount : (((eraseAtoms M {a}).dartsAt b).filter (IsBridge (eraseAtoms M {a}))).card = 1) :
    ActualGoodConfiguration M a := by
  classical
  let N := eraseAtoms M {a}
  have hbOld := (mem_sdiff.mp hb).1
  have hba : b ≠ a := by simpa only [mem_singleton] using (mem_sdiff.mp hb).2
  obtain ⟨e,hset⟩ := card_eq_one.mp hcount
  have heMem : e ∈ (N.dartsAt b).filter (IsBridge N) := by rw [hset]; simp
  have heB := (mem_filter.mp heMem).2
  have heAtom : M.atom e.val = b := (Mole.mem_dartsAt N b e).mp (mem_filter.mp heMem).1
  obtain ⟨U,q,hU,hQcases,hPostCut,hOldCard⟩ :=
    exists_old_two_boundary_side_of_post_bridge M hI.bridgeless a ha3 e heB
  obtain ⟨x,hx,hOldCut,hqmx⟩ := old_two_boundary_eq_bridge_and_first_edge M a U hU q hPostCut hOldCard
  have hUOld : U ⊆ M.atoms := fun z hz => (mem_sdiff.mp (hU hz)).1
  have haNotU : a ∉ U := fun h => (mem_sdiff.mp (hU h)).2 (mem_singleton_self a)
  have heDistinct := retained_ne_first_incidence M a e hx
  have hFirst := circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless ha ha3
  have hSecond := circuitRank_erase_three_one_incident_bridge N (fun z => hI.loopless z.val) hb hb3 hcount
  have hLoss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3 := by
    rw [← circuitRank_erase_erase_singleton_eq M a b]
    change M.circuitRank - (eraseAtoms N {b}).circuitRank = 3
    change N.circuitRank = M.circuitRank - 2 at hFirst
    omega
  rcases old_star_cases_of_post_degree_three M hI.molecule a b hb hb3 with hOld3 | hOld4
  · obtain ⟨A⟩ := exists_star3_remainder M ha3 hx
    obtain ⟨B⟩ := exists_star3_remainder M hOld3.1 heAtom
    rcases hQcases with hqe | hqme
    · have hcut : boundaryDarts M U = {e.val,M.mate x} := by simpa only [hqe] using hOldCut
      exact .affineCubic b hbOld (Ne.symm hba) x e.val A B heDistinct.1 heDistinct.2 true U hUOld hcut hLoss
    · rw [hqme] at hOldCut
      change boundaryDarts M U = {M.mate e.val,M.mate x} at hOldCut
      exact .affineCubic b hbOld (Ne.symm hba) x e.val A B heDistinct.1 heDistinct.2 false U hUOld hOldCut hLoss
  · obtain ⟨hb4,p,hp,hpb,hRemoved,hOldStar⟩ := hOld4
    have heP := retained_ne_first_incidence M a e hp
    obtain ⟨B⟩ := exists_star4_remainder M hb4 hpb heAtom (Ne.symm heP.2)
    by_cases hxp : x = p
    · obtain ⟨A⟩ := exists_star3_remainder M ha3 hp
      have hbU : b ∈ U := by
        have hh : M.mate x ∈ boundaryDarts M U := by rw [hOldCut]; simp
        simpa only [hxp,hpb] using (mem_filter.mp hh).2.1
      have hqe : q = e := single_boundary_bridge_dart_eq_of_joint_mem N U hPostCut hQcases
        (by change M.atom e.val ∈ U; rw [heAtom]; exact hbU)
      have hcut : boundaryDarts M U = {M.mate p,e.val} := by
        rw [hqe,hxp] at hOldCut
        rw [hOldCut,pair_comm]
      have hOut := out_eq_of_joint_two_boundary_no_beta M hb4 hpb heAtom
        (fun z _ => hI.bridgeless z) hI.noBeta U hcut
      have hSigns := remaining_out_of_four_star_pair_eq M hI.molecule hbOld
        B.xy B.xr B.xs B.yr B.ys B.rs B.star hOut
      have hSame : M.out B.s = M.out B.r := hSigns.2.trans hSigns.1.symm
      exact .positiveQuartic b hbOld (Ne.symm hba) p (M.mate p) e.val A B hSame
        (firstProfileCut_mate_first M p A.y A.z) (firstProfileCut_of_post_bridge M a p A e heB) hLoss
    · have hqeNot : q ≠ e := by
        intro hqe
        have heU : e.val ∈ boundaryDarts M U := by rw [hOldCut,hqe]; simp
        have hbU : b ∈ U := heAtom ▸ (mem_filter.mp heU).2.1
        have hpU : M.mate p ∈ boundaryDarts M U := mem_filter.mpr
          ⟨mem_univ _,hpb.symm ▸ hbU,by simpa only [M.mate_mate,hp] using haNotU⟩
        rw [hOldCut,hqe] at hpU
        simp only [mem_insert,mem_singleton] at hpU
        rcases hpU with h | h
        · exact heP.2 h.symm
        · exact hxp (Mole.mate_injective M h).symm
      have hqme := hQcases.resolve_left hqeNot
      rw [hqme] at hOldCut
      change boundaryDarts M U = {M.mate e.val,M.mate x} at hOldCut
      obtain ⟨z,hpz,hxz,hA⟩ := exists_third_of_star3 M ha3 hp hx (Ne.symm hxp)
      let A : Star3Remainder M a p := ⟨x,z,Ne.symm hxp,hpz,hxz,hA⟩
      exact .affineQuartic b hbOld (Ne.symm hba) p e.val A B heDistinct.1 U hUOld hOldCut hLoss

end WaveTurbulence.MoleProp
