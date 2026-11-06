/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBondMatching
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Directional degree counts through an actual internal-bond bijection -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A tail count in any internal bond enumeration is the actual internal
outgoing degree, including parallel bonds and loops. -/
theorem tail_count (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) :
    ((univ : Finset (Fin m)).filter fun i => M.atom (e i).1=v).card=M.outIn S v := by
  change _=((M.dartsAt v).filter (fun d => M.InGroup S d ∧ M.out d=true)).card
  apply Finset.card_bij (fun i _hi => (e i).1)
  · intro i hi
    have hp := (mem_filter.mp (e i).2).2
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v _).mpr (mem_filter.mp hi).2,hp.2,hp.1⟩
  · intro i _hi j _hj he
    exact e.injective (Subtype.ext he)
  · intro d hd
    have hp := mem_filter.mp hd
    have hdT : d ∈ internalBonds M S := mem_filter.mpr ⟨mem_univ _,hp.2.2,hp.2.1⟩
    obtain ⟨i,he⟩ := e.surjective ⟨d,hdT⟩
    have hval : (e i).1=d := congrArg Subtype.val he
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,hval⟩
    rw [hval]
    exact (Mole.mem_dartsAt M v d).mp hp.1

/-- The head count is the actual incoming degree; mate involution transports
outgoing bond representatives to the unique corresponding incoming darts. -/
theorem head_count (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) :
    ((univ : Finset (Fin m)).filter fun i => M.atom (M.mate (e i).1)=v).card=M.inIn S v := by
  change _=((M.dartsAt v).filter (fun d => M.InGroup S d ∧ M.out d=false)).card
  apply Finset.card_bij (fun i _hi => M.mate (e i).1)
  · intro i hi
    have hp := (mem_filter.mp (e i).2).2
    apply mem_filter.mpr
    refine ⟨(Mole.mem_dartsAt M v _).mpr (mem_filter.mp hi).2,?_,?_⟩
    · exact ⟨hp.2.2,by rw [M.mate_mate]; exact hp.2.1⟩
    · rw [M.out_mate,hp.1]; rfl
  · intro i _hi j _hj he
    exact e.injective (Subtype.ext (Mole.mate_injective M he))
  · intro d hd
    have hp := mem_filter.mp hd
    have hdT : M.mate d ∈ internalBonds M S := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_,hp.2.1.2,?_⟩
      · rw [M.out_mate,hp.2.2]; rfl
      · rw [M.mate_mate]; exact hp.2.1.1
    obtain ⟨i,he⟩ := e.surjective ⟨M.mate d,hdT⟩
    have hval : M.mate (e i).1=d := by rw [congrArg Subtype.val he,M.mate_mate]
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,hval⟩
    rw [hval]
    exact (Mole.mem_dartsAt M v d).mp hp.1

end WaveTurbulence.Vine.Param
