/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
public import WaveTurbulence.Foundations.Molecule.Degen.Bridges
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # Actual singleton cuts and uniqueness on bridge-only molecules

DH21 Lemma 9.14 as consumed in DH23 Proposition 10.1. No conservation
parameter is required to vanish at a degree-four atom.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def bridgeSide (M : Molecule V D) (e : D) : Finset V := by
  classical
  exact M.atoms.filter (Relation.EqvGen (Degen.AdjWithoutBond M e) (M.atom e))

theorem bridgeSide_subset (M : Molecule V D) (e : D) : bridgeSide M e ⊆ M.atoms := by
  classical
  exact filter_subset _ _

/-- The endpoint component after deleting a bridge has exactly that bond
as boundary. This derives a cut from the actual bridge predicate. -/
theorem boundary_bridgeSide (M : Molecule V D) (e : D) (he : Degen.IsBridge M e) :
    Degen.boundaryDarts M (bridgeSide M e) = {e} := by
  classical
  have hin : M.atom e ∈ bridgeSide M e := mem_filter.mpr ⟨M.atom_mem e,Relation.EqvGen.refl _⟩
  have hout : M.atom (M.mate e) ∉ bridgeSide M e := by
    intro h
    exact he (mem_filter.mp h).2
  ext x
  simp only [Degen.boundaryDarts,mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,hmx⟩
    by_cases hxe : x = e
    · exact hxe
    by_cases hxme : x = M.mate e
    · subst x
      exact False.elim (hout hx)
    have hstep : Degen.AdjWithoutBond M e (M.atom x) (M.atom (M.mate x)) :=
      ⟨x,rfl,rfl,hxe,hxme⟩
    have hpath := Relation.EqvGen.trans _ _ _ (mem_filter.mp hx).2 (Relation.EqvGen.rel _ _ hstep)
    exact False.elim (hmx (mem_filter.mpr ⟨M.atom_mem _,hpath⟩))
  · rintro rfl
    exact ⟨hin,hout⟩

/-- Every bridge label is determined by actual fixed conservation data. -/
theorem bridge_label_unique (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {w : Mom d} {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L w c κ) (hd' : M.IsDecoration L w c κ')
    (e : D) (he : Degen.IsBridge M e) : κ e = κ' e := by
  exact Degen.coset_label_injective hL w (Degen.single_boundary_momentum_unique M hd hd'
    (bridgeSide M e) (bridgeSide_subset M e) (boundary_bridgeSide M e he))

/-- In a bridge-only graph all decorations with the same source charges agree. -/
theorem decoration_unique_of_all_bridges (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {w : Mom d} {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L w c κ) (hd' : M.IsDecoration L w c κ')
    (hb : ∀ e : D, Degen.IsBridge M e) : κ = κ' := by
  funext e
  exact bridge_label_unique M hL hd hd' e (hb e)

/-- DH23 Proposition 10.1's zero-circuit counting base: no label choices
remain on a bridge-only graph, even with arbitrary c at degree four. -/
theorem countEFree_le_one_of_all_bridges (M : Molecule V D) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hb : ∀ e : D, Degen.IsBridge M e) : countEFree M L γ δ w Adm ≤ 1 := by
  unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro κ hκ κ' hκ'
  exact decoration_unique_of_all_bridges M hL hκ.1 hκ'.1 hb

end WaveTurbulence.MoleProp
