/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemovalJoints
import Mathlib.Tactic

/-! # External edges survive adjoint removal -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
/-- Any atom outside a removed interior survives. -/
theorem remainingAtoms_single_mem (S : Finset V) (P : RemovalPiece V D) {v : V}
    (hv : v ∈ S) (hi : v ∉ P.interior) : v ∈ remainingAtoms S [P] := by
  refine mem_filter.mpr ⟨hv,?_⟩
  intro Q hQ
  simpa only [List.mem_singleton.mp hQ] using hi

/-- An external edge with retained endpoints survives adjoint removal. -/
theorem adjointRemoval_external_adj (M : Molecule V D) (S A : Finset V) (a b : V) (e : D)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (hui : u ∉ A \ {a,b}) (hvi : v ∉ A \ {a,b})
    (hext : ¬(u ∈ A ∧ v ∈ A)) (hAdj : M.Adj u v) :
    (removeBlocks M S [adjointRemoval M A a b e]).Adj u v := by
  obtain ⟨d,hdu,hdv⟩ := hAdj
  have hd : ¬M.InGroup A d := by
    intro hh
    exact hext ⟨hdu ▸ hh.1,hdv ▸ hh.2⟩
  have hdm : ¬M.InGroup A (M.mate d) := by
    intro hh
    apply hd
    exact ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩
  have hk : KeepDart M S [adjointRemoval M A a b e] d := by
    refine ⟨?_,?_,?_⟩
    · rw [hdu]
      exact remainingAtoms_single_mem S _ hu hui
    · rw [hdv]
      exact remainingAtoms_single_mem S _ hv hvi
    · intro P hP
      have he := List.mem_singleton.mp hP
      subst P
      constructor
      · intro hm
        exact hd (mem_filter.mp (mem_sdiff.mp hm).1).2
      · intro hm
        exact hdm (mem_filter.mp (mem_sdiff.mp hm).1).2
  exact ⟨⟨d,hk⟩,hdu,hdv⟩

end WaveTurbulence.Vine
