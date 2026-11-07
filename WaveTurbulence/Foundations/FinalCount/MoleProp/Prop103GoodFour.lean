/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodSelectorSupport
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103IncidentBridgeRemoval
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103ThreeTargetStar
import Mathlib.Tactic

/-! # The actual quartic two-bridge good configuration -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The temporary degree-four/two-bridge case internally chooses the two
bridges and all stars. Equal directions give the positive quartic output;
opposite directions produce all three actual OLD cut equations. -/
theorem select_good_post_degree_four (M : Molecule V D) (hI : SearchInput M)
    {a b : V} (ha : a ∈ M.atoms) (ha3 : M.deg a = 3)
    (hb : b ∈ (eraseAtoms M {a}).atoms) (hb4 : (eraseAtoms M {a}).deg b = 4)
    [DecidablePred (IsBridge (eraseAtoms M {a}))]
    (hcount : (((eraseAtoms M {a}).dartsAt b).filter (IsBridge (eraseAtoms M {a}))).card = 2) :
    ActualGoodConfiguration M a := by
  classical
  let N := eraseAtoms M {a}
  have hbOld := (mem_sdiff.mp hb).1
  have hba : b ≠ a := by simpa only [mem_singleton] using (mem_sdiff.mp hb).2
  obtain ⟨e,f,hef,hset⟩ := card_eq_two.mp hcount
  have heMem : e ∈ (N.dartsAt b).filter (IsBridge N) := by rw [hset]; simp
  have hfMem : f ∈ (N.dartsAt b).filter (IsBridge N) := by rw [hset]; simp
  have heB := (mem_filter.mp heMem).2
  have hfB := (mem_filter.mp hfMem).2
  have heAtom : M.atom e.val = b := (Mole.mem_dartsAt N b e).mp (mem_filter.mp heMem).1
  have hfAtom : M.atom f.val = b := (Mole.mem_dartsAt N b f).mp (mem_filter.mp hfMem).1
  have hfar : N.atom (N.mate e) ≠ b := fun h => hI.loopless e.val (heAtom.trans h.symm)
  have hfMate : f ≠ N.mate e := by
    intro h
    have hh := hfAtom
    rw [h] at hh
    exact hfar hh
  have hD : f ≠ e ∧ f ≠ N.mate e := ⟨Ne.symm hef,hfMate⟩
  have hOld4 : M.deg b = 4 := by
    have hEq := deg_eraseAtoms_add_removed M {a} (mem_sdiff.mp hb).2
    have hCap := Mole.deg_le_four M hI.molecule hbOld
    omega
  have hevalf : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  obtain ⟨B⟩ := exists_star4_remainder M hOld4 heAtom hfAtom hevalf
  have hFirst := circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless ha ha3
  have hSecond := circuitRank_erase_four_two_incident_bridges N (fun z => hI.loopless z.val) hb hb4 hcount
  have hLoss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3 := by
    rw [← circuitRank_erase_erase_singleton_eq M a b]
    change M.circuitRank - (eraseAtoms N {b}).circuitRank = 3
    change N.circuitRank = M.circuitRank - 2 at hFirst
    omega
  by_cases hOut : M.out e.val = M.out f.val
  · obtain ⟨x,⟨A⟩⟩ := exists_star3_order M a ha3
    have hSigns := remaining_out_of_four_star_pair_eq M hI.molecule hbOld
      B.xy B.xr B.xs B.yr B.ys B.rs B.star hOut
    exact .positiveQuartic b hbOld (Ne.symm hba) x e.val f.val A B
      (hSigns.2.trans hSigns.1.symm)
      (firstProfileCut_of_post_bridge M a x A e heB) (firstProfileCut_of_post_bridge M a x A f hfB) hLoss
  · let P := eraseTwoBonds N e f hD
    let U₀ := componentSet P (N.atom e)
    let U₁ := componentSet P (N.atom (N.mate e))
    let U₂ := componentSet P (N.atom (N.mate f))
    obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz,hA,hcut₀,hcut₁,hcut₂⟩ :=
      exists_first_star_and_old_cuts_of_opposite_post_bridges M hI.molecule hI.bridgeless hI.noBeta
        a ha3 e f hD heB hfB (hfAtom.trans heAtom.symm) (by simpa only [heAtom] using hb4) hOut
    let A : Star3Remainder M a x := ⟨y,z,hxy,hxz,hyz,hA⟩
    have hsub (u : V) : componentSet P u ⊆ M.atoms := by
      intro w hw
      exact (mem_sdiff.mp ((mem_componentSet P u w).mp hw).1).1
    exact .threeCutQuartic b hbOld (Ne.symm hba) x e.val f.val A B
      (retained_ne_first_incidence M a e hx).2 (retained_ne_first_incidence M a f hx).2
      U₀ U₁ U₂ (hsub _) (hsub _) (hsub _) hcut₀ hcut₁ hcut₂ hLoss

end WaveTurbulence.MoleProp
