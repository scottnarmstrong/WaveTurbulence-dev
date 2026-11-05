/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreBondCounts
import Mathlib.Tactic

/-! # Unexpanded slots retain their original rail bonds -/

public section
namespace WaveTurbulence.Vine

/-- A bond appearing in no slot survives the entire instruction list. -/
theorem mem_fold_insertRungs_bonds (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (T : VineTemplate) (e : ℕ×ℕ) (he : e ∈ T.bonds) (hn : e ∉ slotMembers xs) :
    e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds := by
  apply List.count_pos_iff.mp
  apply (List.count_pos_iff.mpr he).trans_le
  apply count_le_fold_insertRungs
  intro sk hsk
  constructor
  · intro hh
    apply hn
    apply List.mem_flatMap.mpr
    refine ⟨sk,hsk,?_⟩
    rw [hh]
    exact List.mem_cons_self
  · intro hh
    apply hn
    apply List.mem_flatMap.mpr
    refine ⟨sk,hsk,?_⟩
    rw [hh]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A rail at a zero-rung slot remains present throughout a ready fold.
Distinct slot members ensure no other instruction can erase this rail. -/
theorem zero_slot_bond_mem_fold (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (e : ℕ×ℕ)
    (hready : (slotMembers xs).Nodup) (hslot : (s,0) ∈ xs)
    (hes : e=s.1 ∨ e=s.2) (he : e ∈ T.bonds) :
    e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds := by
  induction xs generalizing T with
  | nil => cases hslot
  | cons sk xs ih =>
    have hr : (sk.1.1::sk.1.2::slotMembers xs).Nodup := hready
    obtain ⟨h1,hr⟩ := List.nodup_cons.mp hr
    obtain ⟨h2,htail⟩ := List.nodup_cons.mp hr
    rcases List.mem_cons.mp hslot with hhead | htailSlot
    · subst sk
      rw [List.foldl_cons,insertRungs_zero]
      apply mem_fold_insertRungs_bonds xs T e he
      rcases hes with rfl | rfl
      · intro hm
        exact h1 (List.mem_cons_of_mem _ hm)
      · exact h2
    · have hetail : e ∈ slotMembers xs := by
        apply List.mem_flatMap.mpr
        refine ⟨(s,0),htailSlot,?_⟩
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using hes
      have he1 : e ≠ sk.1.1 := by
        intro hh
        exact h1 (List.mem_cons_of_mem _ (hh ▸ hetail))
      have he2 : e ≠ sk.1.2 := by
        intro hh
        exact h2 (hh ▸ hetail)
      rw [List.foldl_cons]
      exact ih _ htail htailSlot (mem_insertRungs_bonds he he1 he2 sk.2)

/-- The source slot list supplies the distinctness needed by zero-slot
preservation. The length condition is exactly the pinned realization's. -/
theorem expand_slotMembers_ready (X : VineType) (ks : List ℕ)
    (hk : ks.length=X.template.slots.length) :
    (slotMembers (X.template.slots.zip ks)).Nodup ∧
      ∀ e ∈ slotMembers (X.template.slots.zip ks),e ∈ X.template.bonds := by
  have he : slotMembers (X.template.slots.zip ks)=X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := ks) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  rw [he]
  exact template_slots_ready X

end WaveTurbulence.Vine
