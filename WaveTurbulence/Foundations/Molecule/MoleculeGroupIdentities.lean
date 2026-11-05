/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Internal-degree identities for overlapping atomic groups -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- For an atom common to A and B, incidence multiplicities satisfy the
ordinary union/intersection identity, including self-loops. -/
theorem degIn_union_add_inter (A B : Finset V) {v : V} (hA : v ∈ A) (hB : v ∈ B) :
    M.degIn (A ∪ B) v + M.degIn (A ∩ B) v = M.degIn A v + M.degIn B v := by
  classical
  let DA := (M.dartsAt v).filter (M.InGroup A)
  let DB := (M.dartsAt v).filter (M.InGroup B)
  have hu : (M.dartsAt v).filter (M.InGroup (A ∪ B)) = DA ∪ DB := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_union,mem_dartsAt,Molecule.InGroup,DA,DB]
    by_cases hx : M.atom x = v
    · simp [hx,hA,hB]
    · simp [hx]
  have hi : (M.dartsAt v).filter (M.InGroup (A ∩ B)) = DA ∩ DB := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_inter,mem_dartsAt,Molecule.InGroup,DA,DB]
    tauto
  unfold Molecule.degIn
  rw [hu,hi]
  exact Finset.card_union_add_card_inter DA DB

/-- Internal degree is monotone in the atomic group. -/
theorem degIn_mono {A B : Finset V} (hAB : A ⊆ B) (v : V) : M.degIn A v ≤ M.degIn B v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxv,hxA,hxmA⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxv,hAB hxA,hAB hxmA⟩

/-- A full interior incidence count forces the actual ambient degree four. -/
theorem deg_eq_four_of_degIn (hM : M.IsMolecule) {S : Finset V} {v : V}
    (hv : v ∈ M.atoms) (hd : M.degIn S v = 4) : M.deg v = 4 := by
  have h1 := degIn_le_deg M S v
  have h2 := deg_le_four M hM hv
  omega

omit [Fintype D] in
/-- Every proper internal subset of a nonempty connected group has an
adjacent atom outside it, in the actual induced graph. -/
theorem connected_group_boundary {S T : Finset V} (hT : T ⊆ S) (hne : T.Nonempty)
    (hproper : ¬ S ⊆ T)
    (hconn : ∀ u ∈ S, ∀ v ∈ S, (induced M S).SameComponent u v) :
    ∃ u ∈ T, ∃ v ∈ S, v ∉ T ∧ M.Adj u v := by
  by_contra h
  push Not at h
  have hclosed : ∀ {u v}, (induced M S).SameComponent u v → (u ∈ T ↔ v ∈ T) := by
    intro u v hp
    induction hp with
    | rel a b hab =>
      have hh := (induced_adj_iff M S a b).mp hab
      exact ⟨fun ha => by by_contra hb; exact h a ha b hh.2.2 hb hh.1,
        fun hb => by by_contra ha; exact h b hb a hh.2.1 ha (adj_symmetric M hh.1)⟩
    | refl => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  obtain ⟨u,hu⟩ := hne
  obtain ⟨v,hv,hvT⟩ := Finset.not_subset.mp hproper
  exact hvT ((hclosed (hconn u (hT hu) v hv)).mp hu)

end WaveTurbulence.Mole
