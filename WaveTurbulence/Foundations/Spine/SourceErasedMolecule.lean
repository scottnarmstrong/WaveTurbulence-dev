/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
/-! Deleting a designated bond preserves the actual molecule axioms. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence.Mole

theorem source_eraseBond_isMolecule {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule) (e : D) :
    (Molecule.eraseBond M e).IsMolecule := by
  classical
  let E := Molecule.eraseBond M e
  have hout (v : V) : E.outdeg v ≤ M.outdeg v := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      obtain ⟨hxv, hxo⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_dartsAt M v x.1).mpr ((mem_dartsAt E v x).mp hxv), hxo⟩
    · exact fun _ _ _ _ h => Subtype.ext h
  have hin (v : V) : E.indeg v ≤ M.indeg v := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      obtain ⟨hxv, hxo⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_dartsAt M v x.1).mpr ((mem_dartsAt E v x).mp hxv), hxo⟩
    · exact fun _ _ _ _ h => Subtype.ext h
  refine ⟨fun v hv => ⟨(hout v).trans (hM.1 v hv).1, (hin v).trans (hM.1 v hv).2⟩, ?_⟩
  intro v hv
  by_contra hnone
  let S := M.atoms.filter (fun u => E.SameComponent v u)
  have hsub : S ⊆ M.atoms := filter_subset _ _
  have hvS : v ∈ S := mem_filter.mpr ⟨hv, sameComponent_refl E v⟩
  have hdeg (u : V) (hu : u ∈ S) : E.deg u = 4 := by
    by_contra hne
    exact hnone ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2, hne⟩
  apply no_saturated_group M hM hsub ⟨v, hvS⟩
  intro u hu
  have hmap : Set.MapsTo (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => x.1)
      (E.dartsAt u : Set {x : D // x ≠ e ∧ x ≠ M.mate e})
      ((M.dartsAt u).filter (M.InGroup S) : Set D) := by
    intro x hx
    have hxu : E.atom x = u := (mem_dartsAt E u x).mp hx
    have hmate : E.atom (E.mate x) ∈ S := by
      apply mem_filter.mpr
      refine ⟨E.atom_mem _, ?_⟩
      exact sameComponent_trans E (mem_filter.mp hu).2
        (sameComponent_of_adj E ⟨x, hxu, rfl⟩)
    exact mem_filter.mpr ⟨(mem_dartsAt M u x.1).mpr hxu,
      hxu.symm ▸ hu, hmate⟩
  have hlow := Finset.card_le_card_of_injOn Subtype.val hmap
    (fun _ _ _ _ h => Subtype.ext h)
  have hupper := (degIn_le_deg M S u).trans (deg_le_four M hM (hsub hu))
  change E.deg u ≤ M.degIn S u at hlow
  rw [hdeg u hu] at hlow
  omega

end WaveTurbulence.LGSpine
