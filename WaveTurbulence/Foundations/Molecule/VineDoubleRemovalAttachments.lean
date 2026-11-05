/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoubleRemovalRails
import Mathlib.Tactic

/-! # At least one normal-center attachment survives disjoint double removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An edge not internal to any type-I removal survives as an actual edge. -/
theorem typeI_removal_adj_of_no_piece (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (ha : M.Adj u v)
    (hn : ∀ P ∈ ps,¬(u ∈ P.atoms ∧ v ∈ P.atoms)) :
    (removeBlocks M S ps).Adj u v := by
  classical
  obtain ⟨d,hdu,hdv⟩ := ha
  have hr := remainingAtoms_eq_of_typeI M S ps hI
  have hk : KeepDart M S ps d := by
    refine ⟨hr.symm ▸ (hdu.symm ▸ hu),hr.symm ▸ (hdv.symm ▸ hv),?_⟩
    intro P hP
    rw [hD P hP]
    constructor
    · intro hm
      have hh := (mem_filter.mp hm).2
      exact hn P hP ⟨hdu ▸ hh.1,hdv ▸ hh.2⟩
    · intro hm
      have hh := (mem_filter.mp hm).2
      have hlast : M.atom d ∈ P.atoms := by simpa only [M.mate_mate] using hh.2
      exact hn P hP ⟨hdu ▸ hlast,hdv ▸ hh.1⟩
  exact ⟨⟨d,hk⟩,hdu,hdv⟩

/-- Two distinct neighbor attachments cannot both be removed by disjoint
type-I pieces. The surviving edge attaches a normal center to its backbone. -/
theorem typeI_removal_one_attachment (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    {u v w : V} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hav : M.Adj u v) (haw : M.Adj u w) :
    (removeBlocks M S ps).Adj u v ∨ (removeBlocks M S ps).Adj u w := by
  rcases typeI_family_keeps_one_neighbor M ps hI hdis huv huw hvw with h | h
  · exact Or.inl (typeI_removal_adj_of_no_piece M S ps hI hD hu hv hav h)
  · exact Or.inr (typeI_removal_adj_of_no_piece M S ps hI hD hu hw haw h)

end WaveTurbulence.Vine
