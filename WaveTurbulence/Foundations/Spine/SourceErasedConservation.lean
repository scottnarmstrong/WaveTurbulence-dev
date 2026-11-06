/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceErasedMolecule
public import WaveTurbulence.Foundations.Molecule.MoleculeDecorations
/-! Full-degree flow is unchanged by a bond deletion; source conservation survives in the adjoint. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence.Mole

theorem source_eraseBond_flow_of_deg_four {V D W : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] [AddCommGroup W] [Module ℝ W]
    (M : Molecule V D) (hM : M.IsMolecule) (e : D) (v : V) (hv : v ∈ M.atoms)
    (hdeg : (Molecule.eraseBond M e).deg v = 4) (k : D → W) :
    (∑ x ∈ (Molecule.eraseBond M e).dartsAt v, (Molecule.eraseBond M e).dartSign x • k x.1) =
      ∑ x ∈ M.dartsAt v, M.dartSign x • k x := by
  classical
  let E := Molecule.eraseBond M e
  have hmap : Set.MapsTo (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => x.1)
      (E.dartsAt v : Set {x : D // x ≠ e ∧ x ≠ M.mate e}) (M.dartsAt v : Set D) := by
    intro x hx
    exact (mem_dartsAt M v x.1).mpr ((mem_dartsAt E v x).mp hx)
  have hinj : Set.InjOn (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => x.1) (E.dartsAt v) :=
    fun _ _ _ _ h => Subtype.ext h
  have hc : (M.dartsAt v).card ≤ (E.dartsAt v).card := by
    change M.deg v ≤ E.deg v
    rw [hdeg]
    exact deg_le_four M hM hv
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmap hinj hc
  exact Finset.sum_nbij Subtype.val hmap hinj hsurj (fun _ _ => rfl)

theorem source_eraseBond_conservation {V D W : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] [AddCommGroup W] [Module ℝ W]
    (M : Molecule V D) (hM : M.IsMolecule) (e : D) (k : D → W)
    (hcons : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0) :
    ∀ v ∈ (Molecule.eraseBond M e).atoms, (Molecule.eraseBond M e).deg v = 4 →
      ∑ x ∈ (Molecule.eraseBond M e).dartsAt v, (Molecule.eraseBond M e).dartSign x • k x.1 = 0 := by
  intro v hv hdeg
  rw [source_eraseBond_flow_of_deg_four M hM e v hv hdeg k]
  apply hcons v hv
  have hcard : (Molecule.eraseBond M e).deg v ≤ M.deg v := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      exact (mem_dartsAt M v x.1).mpr ((mem_dartsAt (Molecule.eraseBond M e) v x).mp hx)
    · exact fun _ _ _ _ h => Subtype.ext h
  have hh := deg_le_four M hM hv
  omega

end WaveTurbulence.LGSpine
