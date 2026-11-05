/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
import Mathlib.Tactic

/-! # Bond counts of full vine expansions (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- A bond distinct from both replaced bonds survives insertion. -/
theorem mem_insertRungs_bonds {T : VineTemplate} {s : (ℕ×ℕ)×(ℕ×ℕ)} {e : ℕ×ℕ}
    (he : e ∈ T.bonds) (h1 : e ≠ s.1) (h2 : e ≠ s.2) (k : ℕ) :
    e ∈ (insertRungs T s k).bonds := by
  by_cases hk : k=0
  · simpa only [hk,insertRungs_zero] using he
  · simp only [insertRungs,hk,ite_false]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact (List.mem_erase_of_ne h2).mpr ((List.mem_erase_of_ne h1).mpr he)

/-- The slot members of a list of insertion instructions. -/
@[expose] def slotMembers (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) : List (ℕ×ℕ) :=
  xs.flatMap fun sk => [sk.1.1,sk.1.2]

/-- Distinct slot members remain available throughout insertion, giving the
exact net increment four per rung for an arbitrary instruction list. -/
theorem fold_insertRungs_bonds (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ))
    (T : VineTemplate) (hn : (slotMembers xs).Nodup)
    (hm : ∀ e ∈ slotMembers xs, e ∈ T.bonds) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.length =
      T.bonds.length+4*(xs.map Prod.snd).sum := by
  induction xs generalizing T with
  | nil => simp
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
    rw [List.foldl_cons,ih _ htail hsurvive,
      insertRungs_bonds T sk.1 sk.2 hmem1 ((List.mem_erase_of_ne hne).mpr hmem2)]
    simp only [List.map_cons,List.sum_cons]
    omega

/-- All base-template slot members are distinct and occur in the bond list. -/
theorem template_slots_ready (X : VineType) :
    (X.template.slots.flatMap fun s => [s.1,s.2]).Nodup ∧
      ∀ e ∈ X.template.slots.flatMap (fun s => [s.1,s.2]), e ∈ X.template.bonds := by
  cases X <;> decide

/-- The complete expansion adds exactly four bonds per rung. -/
theorem expand_bonds (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    (X.expand k).bonds.length = X.template.bonds.length+4*k.sum := by
  have hmap : (X.template.slots.zip k).map Prod.snd = k :=
    List.map_snd_zip hk.le
  have hslots : slotMembers (X.template.slots.zip k) =
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hready := template_slots_ready X
  have hh := fold_insertRungs_bonds (X.template.slots.zip k) X.template
    (hslots ▸ hready.1) (hslots ▸ hready.2)
  simpa only [VineType.expand,hmap] using hh

/-- The complete expansion adds exactly two atoms per rung. -/
theorem expand_atoms_exact (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    (X.expand k).n = X.template.n+2*k.sum := by
  rw [expand_atoms,List.map_snd_zip hk.le]

/-- The complete expansion adds exactly one group per rung. -/
theorem expand_groups_exact (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    (X.expand k).groups.length = X.template.groups.length+k.sum := by
  unfold VineType.expand
  rw [fold_insertRungs_groups,List.map_snd_zip hk.le]

/-- Handshaking for every expanded template. -/
theorem expand_bond_atom_count (X : VineType) (k : List ℕ)
    (hk : k.length = X.template.slots.length) :
    (X.expand k).bonds.length+2 = 2*(X.expand k).n := by
  rw [expand_bonds X k hk,expand_atoms_exact X k hk]
  have h := template_bond_count X
  omega

end WaveTurbulence.Vine
