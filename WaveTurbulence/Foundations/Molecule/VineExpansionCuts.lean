/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRawCuts
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotBonds
import Mathlib.Tactic

/-! # The original finite core is a lower bound for every expanded cut -/

public section
namespace WaveTurbulence.Vine

/-- A list of literal rung insertions cannot decrease the cut on any
label set. Slot occurrence assumptions only ensure each replaced occurrence
is available at its insertion step. -/
theorem fold_insertRungs_rawCut_le (W : Finset ℕ)
    (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (hn : (slotMembers xs).Nodup) (hm : ∀ e ∈ slotMembers xs,e ∈ T.bonds) :
    rawCut W T.bonds ≤ rawCut W (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds := by
  induction xs generalizing T with
  | nil => exact le_rfl
  | cons sk xs ih =>
    have hn' : (sk.1.1 :: sk.1.2 :: slotMembers xs).Nodup := hn
    obtain ⟨h1,hn'⟩ := List.nodup_cons.mp hn'
    obtain ⟨h2,htail⟩ := List.nodup_cons.mp hn'
    have hne : sk.1.2 ≠ sk.1.1 := by
      intro he
      exact h1 (List.mem_cons.mpr (Or.inl he.symm))
    have hmem1 := hm sk.1.1 (by simp [slotMembers])
    have hmem2 := hm sk.1.2 (by simp [slotMembers])
    have hsurvive : ∀ e ∈ slotMembers xs,e ∈ (insertRungs T sk.1 sk.2).bonds := by
      intro e he
      apply mem_insertRungs_bonds (hm e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
      · intro heq
        exact h1 (List.mem_cons_of_mem _ (heq ▸ he))
      · intro heq
        exact h2 (heq ▸ he)
    rw [List.foldl_cons]
    exact (insertRungs_rawCut_le W T sk.1 sk.2 hmem1
      ((List.mem_erase_of_ne hne).mpr hmem2)).trans (ih _ htail hsurvive)

/-- TARGET subsetvc, core-cut reduction: every expanded cut dominates the
cut on the pinned finite core, for arbitrary rung counts and label choices. -/
theorem expand_rawCut_le (W : Finset ℕ) (X : VineType) (ks : List ℕ)
    (hk : ks.length=X.template.slots.length) :
    rawCut W X.template.bonds ≤ rawCut W (X.expand ks).bonds := by
  have hr := expand_slotMembers_ready X ks hk
  exact fold_insertRungs_rawCut_le W _ _ hr.1 hr.2

end WaveTurbulence.Vine
