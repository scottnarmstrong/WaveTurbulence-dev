/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaProfile
import Mathlib.Tactic

/-! # The complementary old side of a beta cut -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The other old side has precisely the remaining two star bonds as its
boundary. The statement concerns actual old darts and actual old atom sets. -/
theorem beta_other_side_boundary (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    {v : V} {x y r s : D} (hx : M.atom x = v) (hy : M.atom y = v)
    (hr : M.atom r = v) (hs : M.atom s = v)
    (hxr : x ≠ r) (hxs : x ≠ s) (hyr : y ≠ r) (hys : y ≠ s)
    (hstar : M.dartsAt v = {x,y,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms \ {v})
    (hboundary : boundaryDarts M U = {M.mate x,M.mate y}) :
    boundaryDarts M ((M.atoms \ {v}) \ U) = {M.mate r,M.mate s} := by
  classical
  let T := (M.atoms \ {v}) \ U
  have hvnot : v ∉ U := fun h => (mem_sdiff.mp (hU h)).2 (mem_singleton_self v)
  have hmateInU (z : D) (hzv : M.atom z = v) (hzx : z ≠ x) (hzy : z ≠ y) :
      M.atom (M.mate z) ∉ U := by
    intro hh
    have hb : M.mate z ∈ boundaryDarts M U := by
      apply mem_filter.mpr
      exact ⟨mem_univ _,hh,by simpa only [M.mate_mate,hzv] using hvnot⟩
    rw [hboundary] at hb
    simp only [mem_insert,mem_singleton] at hb
    rcases hb with h | h
    · exact hzx (Mole.mate_injective M h)
    · exact hzy (Mole.mate_injective M h)
  have hrt : M.atom (M.mate r) ∈ T := by
    apply mem_sdiff.mpr
    refine ⟨mem_sdiff.mpr ⟨M.atom_mem _,?_⟩,hmateInU r hr hxr.symm hyr.symm⟩
    simp only [mem_singleton]
    exact fun h => hloop r (hr.trans h.symm)
  have hst : M.atom (M.mate s) ∈ T := by
    apply mem_sdiff.mpr
    refine ⟨mem_sdiff.mpr ⟨M.atom_mem _,?_⟩,hmateInU s hs hxs.symm hys.symm⟩
    simp only [mem_singleton]
    exact fun h => hloop s (hs.trans h.symm)
  have hvnotT : v ∉ T := fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 (mem_singleton_self v)
  ext z
  simp only [boundaryDarts,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · intro hz
    have hza := mem_sdiff.mp hz.1
    have hzv : M.atom (M.mate z) = v := by
      by_contra hn
      have hp : M.atom (M.mate z) ∈ U := by
        by_contra hnu
        exact hz.2 (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _,by simpa only [mem_singleton] using hn⟩,hnu⟩)
      have hm : M.mate z ∈ boundaryDarts M U := by
        apply mem_filter.mpr
        exact ⟨mem_univ _,hp,by simpa only [M.mate_mate] using hza.2⟩
      rw [hboundary] at hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with hm | hm
      · have hh := Mole.mate_injective M hm
        exact (mem_sdiff.mp hza.1).2 (by simpa only [mem_singleton,hh,hx])
      · have hh := Mole.mate_injective M hm
        exact (mem_sdiff.mp hza.1).2 (by simpa only [mem_singleton,hh,hy])
    have hmem : M.mate z ∈ M.dartsAt v := (Mole.mem_dartsAt M v _).mpr hzv
    rw [hstar] at hmem
    simp only [mem_insert,mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · have hz' : z = M.mate x := by simpa only [M.mate_mate] using congrArg M.mate h
      have hh : z ∈ boundaryDarts M U := by rw [hboundary,hz']; simp
      exact False.elim (hza.2 (mem_filter.mp hh).2.1)
    · have hz' : z = M.mate y := by simpa only [M.mate_mate] using congrArg M.mate h
      have hh : z ∈ boundaryDarts M U := by rw [hboundary,hz']; simp
      exact False.elim (hza.2 (mem_filter.mp hh).2.1)
    · exact Or.inl (by simpa only [M.mate_mate] using congrArg M.mate h)
    · exact Or.inr (by simpa only [M.mate_mate] using congrArg M.mate h)
  · rintro (rfl | rfl)
    · exact ⟨hrt,by simpa only [M.mate_mate,hr] using hvnotT⟩
    · exact ⟨hst,by simpa only [M.mate_mate,hs] using hvnotT⟩

end WaveTurbulence.MoleProp
