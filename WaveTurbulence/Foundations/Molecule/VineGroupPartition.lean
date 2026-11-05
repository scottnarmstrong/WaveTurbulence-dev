/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Coherence groups partition the expanded non-joint atoms (TARGET cohmol) -/

public section
namespace WaveTurbulence.Vine

private theorem rung_flatten_perm (us vs : List ℕ) (h : us.length = vs.length) :
    (((us.zip vs).map fun p => [p.1,p.2]).flatten).Perm (us++vs) := by
  induction us generalizing vs with
  | nil => have hv : vs=[] := List.length_eq_zero_iff.mp h.symm; subst vs; exact List.Perm.refl _
  | cons u us ih =>
    cases vs with
    | nil => simp only [List.length_cons,List.length_nil] at h; omega
    | cons v vs =>
      have ht : us.length = vs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h
      change (u :: v :: _).Perm (u :: (us++v::vs))
      exact ((ih vs ht).cons v).trans List.perm_middle.symm |>.cons u

/-- The new two-atom groups cover precisely the freshly allocated atoms. -/
theorem new_groups_partition (n k : ℕ) :
    ((((List.range k).map (n+·)).zip ((List.range k).map (n+k+·))).map
      (fun p => [p.1,p.2])).flatten.Perm (List.range' n (2*k)) := by
  have hp := rung_flatten_perm ((List.range k).map (n+·))
    ((List.range k).map (n+k+·)) (by simp only [List.length_map])
  rw [← List.range'_eq_map_range,← List.range'_eq_map_range,
    List.range'_append_1] at hp
  simpa only [two_mul,List.range'_eq_map_range] using hp

/-- Insertion preserves a partition of the non-joint atoms. -/
theorem insertRungs_groups_partition (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k : ℕ) (hn : 2 ≤ T.n)
    (hg : T.groups.flatten.Perm (List.range' 2 (T.n-2))) :
    (insertRungs T s k).groups.flatten.Perm
      (List.range' 2 ((insertRungs T s k).n-2)) := by
  by_cases hk : k=0
  · simpa only [hk,insertRungs_zero] using hg
  · have hp := hg.append (new_groups_partition T.n k)
    rw [← List.flatten_append] at hp
    have hn' : T.n = 2+(T.n-2) := by omega
    conv at hp => rhs; rhs; rw [hn']
    rw [List.range'_append_1] at hp
    simpa only [insertRungs,hk,ite_false,show T.n+2*k-2 = T.n-2+2*k by omega] using hp

/-- Inserted groups also retain the source size two-or-three condition. -/
theorem insertRungs_group_sizes (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hg : ∀ g ∈ T.groups, g.length=2 ∨ g.length=3) :
    ∀ g ∈ (insertRungs T s k).groups, g.length=2 ∨ g.length=3 := by
  by_cases hk : k=0
  · simpa only [hk,insertRungs_zero] using hg
  · simp only [insertRungs,hk,ite_false,List.mem_append,List.mem_map,Prod.exists]
    intro g h
    rcases h with h | ⟨a,b,_h,rfl⟩
    · exact hg g h
    · exact Or.inl rfl

/-- Partition and size invariants persist through any insertion instruction list. -/
theorem fold_groups_partition (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (hn : 2 ≤ T.n) (hg : T.groups.flatten.Perm (List.range' 2 (T.n-2))) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups.flatten.Perm
      (List.range' 2 ((xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n-2)) := by
  induction xs generalizing T with
  | nil => exact hg
  | cons sk xs ih =>
    exact ih _ (by rw [insertRungs_atoms]; omega)
      (insertRungs_groups_partition T sk.1 sk.2 hn hg)

/-- TARGET cohmol: every expanded vine's groups partition all non-joint atoms. -/
theorem expand_groups_partition (X : VineType) (k : List ℕ) :
    (X.expand k).groups.flatten.Perm (List.range' 2 ((X.expand k).n-2)) := by
  apply fold_groups_partition
  · cases X <;> decide
  · cases X <;> decide

/-- The grouping has no repeated atom. -/
theorem expand_groups_nodup (X : VineType) (k : List ℕ) :
    (X.expand k).groups.flatten.Nodup :=
  (expand_groups_partition X k).nodup_iff.mpr (List.nodup_range' 1 (by decide))

/-- The groups contain exactly the atoms other than the two joints. -/
theorem mem_expand_groups_iff (X : VineType) (k : List ℕ) (v : ℕ) :
    v ∈ (X.expand k).groups.flatten ↔ 2 ≤ v ∧ v < (X.expand k).n := by
  rw [(expand_groups_partition X k).mem_iff,List.mem_range']
  have hn : 2 ≤ (X.expand k).n := by
    rw [expand_atoms]
    have hb : 2 ≤ X.template.n := by cases X <;> decide
    omega
  simp only [one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hv,hvn⟩
    exact ⟨v-2,by omega,by omega⟩

/-- Group sizes remain two or three through a sequence of insertions. -/
theorem fold_group_sizes (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (hg : ∀ g ∈ T.groups, g.length=2 ∨ g.length=3) :
    ∀ g ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).groups,
      g.length=2 ∨ g.length=3 := by
  induction xs generalizing T with
  | nil => exact hg
  | cons sk xs ih => exact ih _ (insertRungs_group_sizes T sk.1 sk.2 hg)

/-- TARGET cohmol: every expanded group contains two or three atoms. -/
theorem expand_group_sizes (X : VineType) (k : List ℕ) :
    ∀ g ∈ (X.expand k).groups, g.length=2 ∨ g.length=3 :=
  fold_group_sizes _ _ (template_group_sizes X)

end WaveTurbulence.Vine
