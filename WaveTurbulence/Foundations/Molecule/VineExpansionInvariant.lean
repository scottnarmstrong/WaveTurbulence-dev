/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDegreeRange
import Mathlib.Tactic

/-! # Structural invariants through all distinct slots (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- An invariant preserved by one available slot is preserved by all slots.
The ready-list premises describe actual distinct slot bonds, not a desired
conclusion of an expansion theorem. -/
theorem fold_insertRungs_invariant (P : VineTemplate → Prop)
    (Allowed : ((ℕ×ℕ)×(ℕ×ℕ)) → Prop)
    (step : ∀ T s k, Allowed s → P T → s.1 ∈ T.bonds → s.2 ∈ T.bonds.erase s.1 →
      P (insertRungs T s k))
    (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) (hT : P T)
    (ha : ∀ sk ∈ xs, Allowed sk.1)
    (hn : (slotMembers xs).Nodup) (hm : ∀ e ∈ slotMembers xs, e ∈ T.bonds) :
    P (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T) := by
  induction xs generalizing T with
  | nil => exact hT
  | cons sk xs ih =>
    have hn' : (sk.1.1 :: sk.1.2 :: slotMembers xs).Nodup := hn
    obtain ⟨h1,hn'⟩ := List.nodup_cons.mp hn'
    obtain ⟨h2,htail⟩ := List.nodup_cons.mp hn'
    have hne : sk.1.2 ≠ sk.1.1 := by
      intro he
      exact h1 (by simp only [List.mem_cons]; exact Or.inl he.symm)
    have hmem1 := hm sk.1.1 (by simp [slotMembers])
    have hmem2 := hm sk.1.2 (by simp [slotMembers])
    have hsurvive : ∀ e ∈ slotMembers xs, e ∈ (insertRungs T sk.1 sk.2).bonds := by
      intro e he
      apply mem_insertRungs_bonds (hm e (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
      · intro heq
        exact h1 (List.mem_cons_of_mem _ (heq ▸ he))
      · intro heq
        exact h2 (heq ▸ he)
    exact ih _
      (step T sk.1 sk.2 (ha sk (List.mem_cons_self)) hT hmem1 ((List.mem_erase_of_ne hne).mpr hmem2))
      (fun q hq => ha q (List.mem_cons_of_mem _ hq)) htail hsurvive

end WaveTurbulence.Vine
