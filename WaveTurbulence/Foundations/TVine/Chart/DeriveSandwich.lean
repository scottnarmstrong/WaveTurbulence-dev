/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveCopy

/-!
# Derivation of the cell decomposition, XV: loops, sandwiches, and the bonds at an atom

* A T-vine has no loop at an interior atom (the closure is loopless, pinned `Molecule.IsClosure`).
* At a loop-free atom the bonds number exactly its degree.
* **Sandwich**: if a piece `C` lies outside a region `Xin` and inside `Xout`, with `Xout ∖ Xin ⊆ C`, every bond at an
  atom of `C` has both ends in `C` or crosses `Xin` or `Xout`.
* A two-bond port has at most one bond at an interior atom (M4 Lemma A).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

/-- **No loop at an interior atom of a T-vine.** -/
theorem no_loop (hT : M.IsTVine S a b) (e : Bond M S) (ha : tl e ≠ a) (hb : tl e ≠ b) : tl e ≠ hd e := by
  intro h
  obtain ⟨-, -, G, G', hC, -, -⟩ := hT
  obtain ⟨-, -, hloop, added, -, hmult⟩ := hC
  have h1 := hmult s(tl e, tl e)
  rw [hloop (tl e)] at h1
  have : 0 < ((M.groupBonds S).filter fun f => a ∉ f ∧ b ∉ f).count s(tl e, tl e) := by
    rw [Multiset.count_pos, Multiset.mem_filter]
    refine ⟨?_, by simp [Sym2.mem_iff, Ne.symm ha], by simp [Sym2.mem_iff, Ne.symm hb]⟩
    unfold Molecule.groupBonds
    rw [Multiset.mem_map]
    refine ⟨e.1, ?_, ?_⟩
    · simp only [Finset.mem_val, mem_filter, mem_univ, true_and]
      exact ⟨(bond_spec e).1, (bond_spec e).2⟩
    · show s(tl e, hd e) = s(tl e, tl e); rw [h]
  omega

/-- At a loop-free atom the bonds number exactly its degree within `S`. -/
theorem card_bondsAt_eq {v : V} (hv : ∀ e : Bond M S, tl e = v → hd e ≠ v) :
    (bondsAt (M := M) (S := S) v).card = M.degIn S v := by
  classical
  have : bondsAt (M := M) (S := S) v = (univ.filter fun e => tl e = v) ∪ (univ.filter fun e => hd e = v) := by
    ext e; simp [bondsAt]
  rw [this, card_union_of_disjoint, card_tl, card_hd, degIn_eq]
  rw [Finset.disjoint_filter]
  intro e _ h1 h2
  exact hv e h1 h2

/-- **The sandwich.** -/
theorem sandwich {C Xin Xout : Finset V} (hCin : ∀ v ∈ C, v ∉ Xin) (hCout : C ⊆ Xout)
    (hdiff : ∀ v ∈ S, v ∈ Xout → v ∉ Xin → v ∈ C) {u : V} (hu : u ∈ C) (e : Bond M S)
    (he : tl e = u ∨ hd e = u) :
    (tl e ∈ C ∧ hd e ∈ C) ∨ Crosses Xin e ∨ Crosses Xout e := by
  unfold Crosses
  have huin := hCin u hu
  have huout := hCout hu
  rcases he with rfl | rfl
  · by_cases h1 : hd e ∈ C
    · exact Or.inl ⟨hu, h1⟩
    · by_cases h2 : hd e ∈ Xin
      · exact Or.inr (Or.inl (Or.inr ⟨h2, huin⟩))
      · have h3 : hd e ∉ Xout := fun h => h1 (hdiff _ (hd_mem e) h h2)
        exact Or.inr (Or.inr (Or.inl ⟨huout, h3⟩))
  · by_cases h1 : tl e ∈ C
    · exact Or.inl ⟨h1, hu⟩
    · by_cases h2 : tl e ∈ Xin
      · exact Or.inr (Or.inl (Or.inl ⟨h2, huin⟩))
      · have h3 : tl e ∉ Xout := fun h => h1 (hdiff _ (tl_mem e) h h2)
        exact Or.inr (Or.inr (Or.inr ⟨huout, h3⟩))

/-- A two-bond port has at most one bond at an interior atom. -/
theorem port_at_most_one {X : Finset V} (π : Port2 M S X a b) {w : V} (hwa : w ≠ a) (hwb : w ≠ b)
    {e f : Bond M S} (he : e ∈ portSet X) (hf : f ∈ portSet X) (hew : tl e = w ∨ hd e = w)
    (hfw : tl f = w ∨ hd f = w) : e = f := by
  rw [π.set_eq, mem_insert, mem_singleton] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · rfl
  · exact absurd ⟨hew, hfw⟩ (π.distinct w hwa hwb)
  · exact absurd ⟨hfw, hew⟩ (π.distinct w hwa hwb)
  · rfl

theorem port_out_unique {X : Finset V} (π : Port2 M S X a b) {e : Bond M S} (he : e ∈ portSet X)
    (hl : tl e ∈ X) : e = π.out := by
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · rfl
  · exact absurd hl π.inn_tl

theorem port_inn_unique {X : Finset V} (π : Port2 M S X a b) {e : Bond M S} (he : e ∈ portSet X)
    (hl : hd e ∈ X) : e = π.inn := by
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact absurd hl π.out_hd
  · rfl

theorem port2_out_eq {X : Finset V} (π π' : Port2 M S X a b) : π.out = π'.out :=
  port_out_unique π' (by rw [π.set_eq]; simp) π.out_tl

theorem port2_inn_eq {X : Finset V} (π π' : Port2 M S X a b) : π.inn = π'.inn :=
  port_inn_unique π' (by rw [π.set_eq]; simp) π.inn_hd

theorem out_mem {X : Finset V} (π : Port2 M S X a b) : π.out ∈ portSet X := by rw [π.set_eq]; simp
theorem inn_mem {X : Finset V} (π : Port2 M S X a b) : π.inn ∈ portSet X := by rw [π.set_eq]; simp

end WaveTurbulence.TVine.Chart
