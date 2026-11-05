/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Exact ambient degree formulas after a designated bond deletion -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Restricting to the entire declared atom group does not change degrees. -/
theorem degIn_atoms (M : Molecule V D) (v : V) : M.degIn M.atoms v=M.deg v := by
  unfold Molecule.degIn Molecule.deg Molecule.InGroup
  simp only [M.atom_mem,true_and,filter_true]

/-- Every filtered ambient degree after deletion is the old dart count
minus exactly the two designated mates. -/
theorem eraseBond_filtered_degree (M : Molecule V D) (e : D) (v : V)
    (P : D → Prop) [DecidablePred P] :
    (((Mole.eraseBond M e).dartsAt v).filter (fun d => P d.1)).card=
      (((M.dartsAt v).filter P) \ {e,M.mate e}).card := by
  apply card_bij (fun d _hd => d.1)
  · intro d hd
    obtain ⟨hdv,hp⟩ := mem_filter.mp hd
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨?_,hp⟩,?_⟩
    · exact (Mole.mem_dartsAt M v d.1).mpr ((Mole.mem_dartsAt (Mole.eraseBond M e) v d).mp hdv)
    · simpa only [mem_insert,mem_singleton,not_or] using d.2
  · intro d _hd f _hf he
    exact Subtype.ext he
  · intro d hd
    obtain ⟨hdv,hdne⟩ := mem_sdiff.mp hd
    have hn : d ≠ e ∧ d ≠ M.mate e := by simpa only [mem_insert,mem_singleton,not_or] using hdne
    refine ⟨⟨d,hn⟩,mem_filter.mpr ⟨?_,(mem_filter.mp hdv).2⟩,rfl⟩
    exact (Mole.mem_dartsAt (Mole.eraseBond M e) v _).mpr
      ((Mole.mem_dartsAt M v d).mp (mem_filter.mp hdv).1)

/-- Deleting a designated bond cannot increase any ambient degree. -/
theorem eraseBond_degree_le (M : Molecule V D) (e : D) (v : V) :
    (Mole.eraseBond M e).outdeg v ≤ M.outdeg v ∧
    (Mole.eraseBond M e).indeg v ≤ M.indeg v ∧ (Mole.eraseBond M e).deg v ≤ M.deg v := by
  have ho := eraseBond_filtered_degree M e v (fun d => M.out d=true)
  have hi := eraseBond_filtered_degree M e v (fun d => M.out d=false)
  have hd := eraseBond_filtered_degree M e v (fun _ => True)
  simp only [filter_true] at hd
  exact ⟨ho.trans_le (card_le_card sdiff_subset),hi.trans_le (card_le_card sdiff_subset),
    hd.trans_le (card_le_card sdiff_subset)⟩

/-- One ambient incidence is removed at each endpoint of a nonloop bond. -/
theorem eraseBond_degree_endpoint (M : Molecule V D) (e : D)
    (hne : M.atom e ≠ M.atom (M.mate e)) :
    (Mole.eraseBond M e).deg (M.atom e)+1=M.deg (M.atom e) := by
  have hh := Mole.eraseBond_degIn_endpoint M e rfl rfl hne (M.atom_mem e) (M.atom_mem (M.mate e))
  rw [degIn_atoms M] at hh
  change (Mole.eraseBond M e).degIn (Mole.eraseBond M e).atoms (M.atom e)+1=_ at hh
  rwa [degIn_atoms (Mole.eraseBond M e)] at hh

/-- The ambient degree does not depend on which mate represents deletion. -/
theorem eraseBond_mate_degree (M : Molecule V D) (e : D) (v : V) :
    (Mole.eraseBond M (M.mate e)).deg v=(Mole.eraseBond M e).deg v := by
  have hh := Mole.eraseBond_mate_degIn M e M.atoms v
  change (Mole.eraseBond M (M.mate e)).degIn (Mole.eraseBond M (M.mate e)).atoms v=
    (Mole.eraseBond M e).degIn (Mole.eraseBond M e).atoms v at hh
  simpa only [degIn_atoms] using hh

end WaveTurbulence.Vine
