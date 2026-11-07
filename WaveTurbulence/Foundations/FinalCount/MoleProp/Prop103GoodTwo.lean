/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodSelectorSupport
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostDegreeCases
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103LocalRemoval
import Mathlib.Tactic

/-! # The actual degree-two good configuration selected after R -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The temporary degree-two/zero-bridge case internally produces the
actual two shared cubic stars and exact total circuit loss three. -/
theorem select_good_post_degree_two (M : Molecule V D) (hI : SearchInput M)
    {a b : V} (ha : a ∈ M.atoms) (ha3 : M.deg a = 3)
    (hb : b ∈ (eraseAtoms M {a}).atoms) (hb2 : (eraseAtoms M {a}).deg b = 2)
    [DecidablePred (IsBridge (eraseAtoms M {a}))]
    (hcount : (((eraseAtoms M {a}).dartsAt b).filter (IsBridge (eraseAtoms M {a}))).card = 0) :
    ActualGoodConfiguration M a := by
  classical
  let N := eraseAtoms M {a}
  have hbOld := (mem_sdiff.mp hb).1
  have hba : b ≠ a := by simpa only [mem_singleton] using (mem_sdiff.mp hb).2
  obtain ⟨hb3,p,hp,hpb,hremoved,hstar⟩ := old_shared_star_of_post_degree_two M hI.simple hI.minDegree a b hb hb2
  obtain ⟨A⟩ := exists_star3_remainder M ha3 hp
  obtain ⟨B⟩ := exists_star3_remainder M hb3 hpb
  have hnb : ∀ e, N.atom e = b → ¬ IsBridge N e := by
    intro e heb hBridge
    have hem : e ∈ (N.dartsAt b).filter (IsBridge N) :=
      mem_filter.mpr ⟨(Mole.mem_dartsAt N b e).mpr heb,hBridge⟩
    have hempty : (N.dartsAt b).filter (IsBridge N) = ∅ := card_eq_zero.mp hcount
    rw [hempty] at hem
    simpa using hem
  have hFirst := circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless ha ha3
  have hSecond := circuitRank_erase_two_of_no_incident_bridges N (fun e => hI.loopless e.val) hb hb2 hnb
  have hLoss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3 := by
    rw [← circuitRank_erase_erase_singleton_eq M a b]
    change M.circuitRank - (eraseAtoms N {b}).circuitRank = 3
    change N.circuitRank = M.circuitRank - 2 at hFirst
    omega
  exact .sharedCubic b hbOld (Ne.symm hba) p A B hLoss

end WaveTurbulence.MoleProp
