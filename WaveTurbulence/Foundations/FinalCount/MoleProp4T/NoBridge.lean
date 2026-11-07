/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Common
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BetaCut
import Mathlib.Tactic

/-! # Even degrees: no bridge

In a molecule whose atoms all have even degree (e.g. a 4-regular pseudomolecule), no bond is a bridge: removing a
bond `ℓ` keeps each component connected. Indeed, if the component `S` of one end of `ℓ` in `𝕄 ∖ ℓ` missed the other
end, then `ℓ` would be the only bond leaving `S`, and the degree sum over `S` would be odd. (Case-4 note, Step 3:
"every edge cut in a graph with all degrees even has even size".)
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
omit [DecidableEq V] [Fintype D] in
/-- The darts inside a mate-closed set come in pairs. -/
theorem even_card_of_mate_closed (M : Molecule V D) (A : Finset D) (hA : ∀ z ∈ A, M.mate z ∈ A) :
    Even A.card := by
  classical
  induction h : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · rw [card_empty] at h; subst h; exact ⟨0, rfl⟩
    · have hmz := hA z hz
      have hne : M.mate z ≠ z := M.mate_ne z
      set A' := (A.erase z).erase (M.mate z)
      have hA' : ∀ w ∈ A', M.mate w ∈ A' := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := mem_erase.mp hw
        obtain ⟨hw3, hw4⟩ := mem_erase.mp hw2
        refine mem_erase.mpr ⟨fun h' => hw3 ?_, mem_erase.mpr ⟨fun h' => hw1 ?_, hA w hw4⟩⟩
        · have := congrArg M.mate h'; rwa [M.mate_mate, M.mate_mate] at this
        · rw [← h', M.mate_mate]
      have hcard : A'.card + 2 = A.card := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hne, hmz⟩), card_erase_of_mem hz]
        have : 2 ≤ A.card := by
          have := card_le_card (show ({z, M.mate z} : Finset D) ⊆ A by
            intro w hw; rcases mem_insert.mp hw with rfl | hw
            · exact hz
            · rw [mem_singleton.mp hw]; exact hmz)
          rw [card_pair hne.symm] at this; exact this
        omega
      have := ih A'.card (by omega) A' hA' rfl
      rw [← h, ← hcard]
      exact this.add even_two

omit [DecidableEq D] in
/-- **No bridge**: in a molecule with all degrees even, removing a bond keeps its ends connected. -/
theorem eraseBond_sameComponent_ends (M : Molecule V D) (heven : ∀ v ∈ M.atoms, Even (M.deg v)) (e : D) :
    (MoleProp.eraseBond M e).SameComponent (M.atom e) (M.atom (M.mate e)) := by
  classical
  by_contra hno
  set N := MoleProp.eraseBond M e
  set S := (Degen.componentSet N (M.atom e))
  have hmem : ∀ v, v ∈ S ↔ v ∈ M.atoms ∧ N.SameComponent (M.atom e) v := fun v => Degen.mem_componentSet N _ v
  have heS : M.atom e ∈ S := (hmem _).mpr ⟨M.atom_mem e, Relation.EqvGen.refl _⟩
  have hmS : M.atom (M.mate e) ∉ S := fun h => hno ((hmem _).mp h).2
  -- every dart of `M` other than `e, mate e` with one end in `S` has both ends in `S`
  have hclosed : ∀ z, z ≠ e → z ≠ M.mate e → M.atom z ∈ S → M.atom (M.mate z) ∈ S := by
    intro z h1 h2 hz
    obtain ⟨_, hc⟩ := (hmem _).mp hz
    refine (hmem _).mpr ⟨M.atom_mem _, Relation.EqvGen.trans _ _ _ hc (Relation.EqvGen.rel _ _ ⟨⟨z, h1, h2⟩, rfl, rfl⟩)⟩
  -- the degree sum over `S` counts the darts at `S`
  let A := univ.filter fun z : D => M.atom z ∈ S
  have hsum : ∑ v ∈ S, M.deg v = A.card := by
    rw [card_eq_sum_card_fiberwise (s := A) (t := S) (f := M.atom) (fun z hz => (mem_filter.mp hz).2)]
    refine sum_congr rfl fun v hv => ?_
    unfold Molecule.deg Molecule.dartsAt
    congr 1; ext z
    simp only [mem_filter, mem_univ, true_and, A]
    exact ⟨fun h => ⟨h ▸ hv, h⟩, fun h => h.2⟩
  -- `A ∖ {e}` is mate-closed
  have heA : e ∈ A := mem_filter.mpr ⟨mem_univ _, heS⟩
  have hmeA : M.mate e ∉ A := by
    intro h; exact hmS (mem_filter.mp h).2
  have hclosedA : ∀ z ∈ A.erase e, M.mate z ∈ A.erase e := by
    intro z hz
    obtain ⟨hze, hzA⟩ := mem_erase.mp hz
    have hzm : z ≠ M.mate e := fun h => hmeA (h ▸ hzA)
    refine mem_erase.mpr ⟨fun h => hzm (by rw [← h, M.mate_mate]), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact hclosed z hze hzm (mem_filter.mp hzA).2
  have hev := even_card_of_mate_closed M _ hclosedA
  rw [card_erase_of_mem heA] at hev
  have hpos : 0 < A.card := card_pos.mpr ⟨e, heA⟩
  have hsev : Even (∑ v ∈ S, M.deg v) := by
    refine Finset.even_sum _ fun v hv => heven v ((hmem v).mp hv).1
  rw [hsum] at hsev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨m, hm⟩ := hsev
  omega

omit [DecidableEq D] in
/-- **Removing a bond from a connected molecule with even degrees keeps it connected.** -/
theorem eraseBond_connected_of_even (M : Molecule V D) (heven : ∀ v ∈ M.atoms, Even (M.deg v))
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) (e : D) :
    ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u v := by
  have hends := eraseBond_sameComponent_ends M heven e
  have key : ∀ a b, M.SameComponent a b → (MoleProp.eraseBond M e).SameComponent a b := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      by_cases h1 : z = e
      · subst h1; exact hends
      by_cases h2 : z = M.mate e
      · subst h2; rw [M.mate_mate]; exact Relation.EqvGen.symm _ _ hends
      exact Relation.EqvGen.rel _ _ ⟨⟨z, h1, h2⟩, rfl, rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro u hu v hv
  exact key u v (hconn u hu v hv)

end WaveTurbulence.MoleProp4
