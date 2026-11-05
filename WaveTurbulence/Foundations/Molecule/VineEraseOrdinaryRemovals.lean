/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
import Mathlib.Tactic

/-! # Ordinary removals transport through a designated outer bond deletion -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The same ordinary atom group and joints, with internal darts taken
in the molecule after the outer designated bond is deleted. -/
@[expose] def eraseOrdinaryPiece (M : Molecule V D) (e : D) (P : RemovalPiece V D) :
    RemovalPiece V {d : D // d ≠ e ∧ d ≠ M.mate e} :=
  blockRemoval (Mole.eraseBond M e) P.atoms P.left P.right

/-- Ordinary atom removal is independent of the outer deleted bond. -/
theorem remainingAtoms_eraseOrdinary (M : Molecule V D) (e : D) (S : Finset V)
    (ps : List (RemovalPiece V D)) :
    remainingAtoms S (ps.map (eraseOrdinaryPiece M e))=remainingAtoms S ps := by
  ext v
  constructor
  · intro hv
    have hh := mem_filter.mp hv
    refine mem_filter.mpr ⟨hh.1,?_⟩
    intro P hP
    exact hh.2 _ (List.mem_map.mpr ⟨P,hP,rfl⟩)
  · intro hv
    have hh := mem_filter.mp hv
    refine mem_filter.mpr ⟨hh.1,?_⟩
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    exact hh.2 P hP

/-- Every surviving adjoint dart also survives the original ordinary
removals, provided their selected darts are the full source internal bonds. -/
theorem keepDart_eraseOrdinary_to (M : Molecule V D) (e : D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (d : {d : D // d ≠ e ∧ d ≠ M.mate e})
    (hd : KeepDart (Mole.eraseBond M e) S (ps.map (eraseOrdinaryPiece M e)) d) :
    KeepDart M S ps d.1 := by
  have hr := remainingAtoms_eraseOrdinary M e S ps
  refine ⟨hr ▸ hd.1,hr ▸ hd.2.1,?_⟩
  intro P hP
  have hPmem : eraseOrdinaryPiece M e P ∈ ps.map (eraseOrdinaryPiece M e) := List.mem_map.mpr ⟨P,hP,rfl⟩
  have hnew := hd.2.2 _ hPmem
  constructor
  · intro hm
    rw [hD P hP] at hm
    have hin := (mem_filter.mp hm).2
    apply hnew.1
    exact mem_filter.mpr ⟨mem_univ _,hin⟩
  · intro hm
    rw [hD P hP] at hm
    have hin := (mem_filter.mp hm).2
    apply hnew.2
    exact mem_filter.mpr ⟨mem_univ _,hin⟩

/-- Paths after deletion of the outer closing bond and ordinary pieces
lift to paths after the same ordinary removals in the original molecule. -/
theorem eraseBond_ordinary_removal_path_to (M : Molecule V D) (e : D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V}
    (hp : (removeBlocks (Mole.eraseBond M e) S (ps.map (eraseOrdinaryPiece M e))).SameComponent u v) :
    (removeBlocks M S ps).SameComponent u v := by
  induction hp with
  | rel u v huv =>
    obtain ⟨d,hdu,hdv⟩ := huv
    have hk := keepDart_eraseOrdinary_to M e S ps hD d.1 d.2
    exact Relation.EqvGen.rel _ _ ⟨⟨d.1.1,hk⟩,hdu,hdv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
