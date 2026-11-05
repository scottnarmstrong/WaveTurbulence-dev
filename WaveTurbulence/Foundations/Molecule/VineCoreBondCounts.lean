/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoubleCountExtraction
public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Core double bonds survive every slot insertion with multiplicity -/

public section
namespace WaveTurbulence.Vine

/-- An edge not replaced at the current slot keeps all its old copies. -/
theorem count_le_insertRungs_bonds (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k : ℕ) (e : ℕ×ℕ) (h1 : e ≠ s.1) (h2 : e ≠ s.2) :
    T.bonds.count e ≤ (insertRungs T s k).bonds.count e := by
  by_cases hk : k=0
  · simp only [insertRungs,hk,ite_true,le_refl]
  · simp only [insertRungs,hk,ite_false,List.count_append,
      List.count_erase_of_ne h1,List.count_erase_of_ne h2]
    omega

/-- Every untouched core bond retains its multiplicity throughout a fold. -/
theorem count_le_fold_insertRungs (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (T : VineTemplate) (e : ℕ×ℕ)
    (he : ∀ sk ∈ xs,e ≠ sk.1.1 ∧ e ≠ sk.1.2) :
    T.bonds.count e ≤ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.count e := by
  induction xs generalizing T with
  | nil => exact le_rfl
  | cons sk xs ih =>
    rw [List.foldl_cons]
    have hh := he sk List.mem_cons_self
    exact (count_le_insertRungs_bonds T sk.1 sk.2 e hh.1 hh.2).trans
      (ih _ (fun z hz => he z (List.mem_cons_of_mem _ hz)))

/-- Both replaceable rail bonds in every pinned slot are single core bonds. -/
theorem template_slot_single (X : VineType) :
    ∀ s ∈ X.template.slots,X.template.bonds.count s.1=1 ∧ X.template.bonds.count s.2=1 := by
  cases X <;> decide

/-- Core double bonds are never slot bonds, so all copies remain after an
arbitrary complete expansion. -/
theorem expand_core_double_count (X : VineType) (ks : List ℕ) (e : ℕ×ℕ)
    (hc : 2 ≤ X.template.bonds.count e) :
    X.template.bonds.count e ≤ (X.expand ks).bonds.count e := by
  apply count_le_fold_insertRungs
  intro sk hsk
  have hs := template_slot_single X sk.1 (List.of_mem_zip hsk).1
  constructor
  · intro he
    rw [he,hs.1] at hc
    omega
  · intro he
    rw [he,hs.2] at hc
    omega

end WaveTurbulence.Vine
