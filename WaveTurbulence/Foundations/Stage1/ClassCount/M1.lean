/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Labelling
public import WaveTurbulence.Foundations.Stage1.ClassCount.ArcCode
public import WaveTurbulence.Foundations.Stage1.ClassCount.Arcs
import Mathlib.Tactic

/-!
# CLASSCOUNT (M1): the arc multiset of a garden with disjoint ladders

For a garden `G` whose molecule has a family of pairwise disjoint ladders `F`, there is a labelling
`ℓ : GBranch G.tree ≃ Fin (nn G)` and a list `L ∈ arcLists n K {0}`, `K = 4 (#free atoms + #ladders)`, whose arc counts
are those of the bonds of `G` (`exists_garden_arcList`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Mole

namespace LadderFam
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {ι : Type}
  (F : LadderFam M ι)

theorem bb_le_two {a b : V} (h : F.Reg a b) : M.bondsBetween a b ≤ 2 := by
  obtain ⟨i, hreg⟩ := h
  rcases hreg with ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact (bb_uv F i j).le
  · exact (bb_vu F i j).le
  · exact (bb_uu F i j.castSucc j.succ (by simp)).le.trans (by norm_num)
  · exact (bb_uu' F i j.succ j.castSucc (by simp)).le.trans (by norm_num)
  · exact (bb_vv F i j.castSucc j.succ (by simp)).le.trans (by norm_num)
  · exact (bb_vv' F i j.succ j.castSucc (by simp)).le.trans (by norm_num)

end LadderFam


/-- The number of atoms. -/
abbrev nn {w : ℕ} (G : Garden w) : ℕ := Fintype.card (GBranch G.tree)

open Classical in
/-- **(M1)**: arc lists of a garden with disjoint ladders. -/
theorem exists_garden_arcList {w : ℕ} (G : Garden w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : LadderFam G.molecule ι) (hM : G.molecule.IsMolecule)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ∃ ℓ : GBranch G.tree ≃ Fin (nn G),
      ∃ L ∈ arcLists (nn G)
          (4 * (G.molecule.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι)
          {fun _ => 0},
        ∀ x : Fin (nn G) × Fin (nn G),
          Fintype.card {b : {y : GardenDart G // G.molecule.out y = true} //
            (ℓ (G.molecule.atom b.1), ℓ (G.molecule.atom (G.molecule.mate b.1))) = x} = L.count x := by
  obtain ⟨ℓ, hℓ⟩ := F.exists_labelling hdisj
  let B := {y : GardenDart G // G.molecule.out y = true}
  let arc : B → Fin (nn G) × Fin (nn G) := fun b => (ℓ (G.molecule.atom b.1), ℓ (G.molecule.atom (G.molecule.mate b.1)))
  let Rg : B → Prop := fun b => F.Reg (G.molecule.atom b.1) (G.molecule.atom (G.molecule.mate b.1))
  have h1 : ∀ b, Rg b → nearPair (nn G) (arc b) := by
    intro b hb
    obtain ⟨hne, h1, h2⟩ := hℓ _ _ hb
    exact ⟨fun h => hne (ℓ.injective h), h1, h2⟩
  have h2 : ∀ x, (univ.filter (fun b : B => Rg b ∧ arc b = x)).card ≤ 2 := by
    intro x
    rcases (univ.filter (fun b : B => Rg b ∧ arc b = x)).eq_empty_or_nonempty with he | ⟨b0, hb0⟩
    · rw [he]; simp
    · have hb0' := Finset.mem_filter.mp hb0
      set a := G.molecule.atom b0.1
      set a' := G.molecule.atom (G.molecule.mate b0.1)
      have hne : a ≠ a' := (hℓ _ _ hb0'.2.1).1
      have hbb : G.molecule.bondsBetween a a' ≤ 2 := F.bb_le_two hb0'.2.1
      have hsub : (univ.filter (fun b : B => Rg b ∧ arc b = x)).card ≤
          ((G.molecule.dartsAt a).filter (fun y => G.molecule.atom (G.molecule.mate y) = a')).card := by
        refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
        · intro b hb
          have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
          have e := hb'.2.2
          have e0 := hb0'.2.2
          rw [← e0] at e
          simp only [arc, Prod.mk.injEq] at e
          rw [Finset.mem_coe, Finset.mem_filter, Mole.mem_dartsAt]
          exact ⟨ℓ.injective e.1, ℓ.injective e.2⟩
        · intro b _ b' _ h
          exact Subtype.ext h
      rw [card_darts_to G.molecule a a' hne] at hsub
      omega
  have h4 : (fun x => (univ.filter (fun b : B => (fun _ => False) b ∧ arc b = x)).card) ∈
      ({fun _ => 0} : Finset (Fin (nn G) × Fin (nn G) → ℕ)) := by
    rw [Finset.mem_singleton]; funext x; simp
  have h5 : (univ.filter (fun b : B => ¬ Rg b ∧ ¬ (fun _ => False) b)).card ≤
      4 * (G.molecule.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι := by
    refine le_trans ?_ (F.card_irrBonds_le hM hdisj)
    refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
    · intro b hb
      have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, b.2, hb'.2.1⟩
    · intro b _ b' _ h
      exact Subtype.ext h
  obtain ⟨L, hL, hcount⟩ := exists_arcList arc Rg (fun _ => False) {fun _ => 0} h1 h2
    (fun b hb => hb.2) h4 h5
  refine ⟨ℓ, L, hL, fun x => ?_⟩
  rw [← hcount x, Fintype.card_subtype]

end WaveTurbulence.ClassCount
