/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.VineSlots
import Mathlib.Tactic

/-! # Incoherent inserted rungs are incoherent groups (TARGET cohmol, layervine)

For every slot `c` the number of rungs `i` with `𝔏_{u_i} ≠ 𝔏_{v_i}` is at most the incoherency index of the
vine (`realizedIncoherencyIndex`): each inserted rung is a group of the expanded template, and the groups
are pairwise distinct.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

theorem fold_groups_mem (xs : List (((ℕ × ℕ) × ℕ × ℕ) × ℕ)) (W : VineTemplate) {g : List ℕ}
    (hg : g ∈ W.groups) : g ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) W).groups := by
  induction xs generalizing W with
  | nil => exact hg
  | cons sk xs ih =>
    apply ih
    by_cases hk : sk.2 = 0
    · simpa [insertRungs, hk] using hg
    · simp only [insertRungs, hk, ite_false, List.mem_append]; exact Or.inl hg

theorem rung_group_mem (U : VineTemplate) (s : (ℕ × ℕ) × ℕ × ℕ) {k i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ k) :
    [U.n + (i - 1), U.n + k + (i - 1)] ∈ (insertRungs U s k).groups := by
  have hk : k ≠ 0 := by omega
  simp only [insertRungs, hk, ite_false, List.mem_append, List.mem_map, Prod.exists]
  right
  refine ⟨U.n + (i - 1), U.n + k + (i - 1), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨i - 1, ?_, ?_⟩
  · simp [List.length_zip]; omega
  · simp [List.getElem_zip]

theorem groups_nodup (X : VineType) (ks : List ℕ) : (X.expand ks).groups.Nodup := by
  have h := List.nodup_flatten.mp (expand_groups_nodup X ks)
  have hsz := expand_group_sizes X ks
  unfold List.Nodup
  apply List.Pairwise.imp_of_mem _ h.2
  intro g g' hg hg' hd heq
  subst heq
  have := hsz g hg
  have hne : g ≠ [] := by rintro rfl; simp at this
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil g hne
  exact hd hx hx

theorem incCnt_slot_le (R : VineRealization M X S a b) (c : Fin X.template.slots.length) (f : V → ℕ) :
    incCnt (fun i => f ((slotQ R c).u i)) (fun i => f ((slotQ R c).v i)) 1 (kSlot R c) ≤
      realizedIncoherencyIndex R f := by
  classical
  set k := kSlot R c with hk
  set Q := slotQ R c with hQ
  -- the incoherent rungs
  set N : Finset ℕ := (Ico 1 (k + 1)).filter (fun i => f (Q.u i) ≠ f (Q.v i)) with hN
  have hcnt : incCnt (fun i => f (Q.u i)) (fun i => f (Q.v i)) 1 k = N.card := by
    unfold incCnt
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : f (Q.u i) = f (Q.v i) <;> simp [h]
  rw [hcnt]
  -- the group of rung i
  set grp : ℕ → List ℕ := fun i => [offSlot R c + (i - 1), offSlot R c + k + (i - 1)] with hgrp
  have hmem : ∀ i, 1 ≤ i → i ≤ k → grp i ∈ (X.expand R.k).groups := by
    intro i hi1 hi2
    have hcl : c.1 < (slotZip R).length := by rw [slotZip_length]; exact c.2
    have hloc : X.template.slots.zip R.k =
        (slotZip R).take c.1 ++ ((slotZip R)[c.1]'hcl) :: (slotZip R).drop (c.1 + 1) := by
      change slotZip R = _
      rw [← List.drop_eq_getElem_cons hcl, List.take_append_drop]
    have hexp : X.expand R.k = ((slotZip R).drop (c.1 + 1)).foldl (fun U sk => insertRungs U sk.1 sk.2)
        (insertRungs (((slotZip R).take c.1).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template)
          ((slotZip R)[c.1]'hcl).1 ((slotZip R)[c.1]'hcl).2) := by
      unfold VineType.expand
      rw [hloc, List.foldl_append, List.foldl_cons]
    rw [hexp]
    apply fold_groups_mem
    have := rung_group_mem (((slotZip R).take c.1).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template)
      ((slotZip R)[c.1]'hcl).1 (k := ((slotZip R)[c.1]'hcl).2) hi1 hi2
    have hn : (((slotZip R).take c.1).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n =
        offSlot R c := by
      rw [fold_insertRungs_atoms]; unfold offSlot; rfl
    rw [hn] at this
    exact this
  -- distinct positions
  have hinj : Set.InjOn grp (N : Set ℕ) := by
    intro i hi j hj h
    simp only [hgrp, List.cons.injEq, and_true] at h
    have hi' := Finset.mem_coe.mp hi
    have hj' := Finset.mem_coe.mp hj
    simp only [hN, mem_filter, mem_Ico] at hi' hj'
    omega
  have hbad : ∀ i ∈ N, ¬ GroupCoherent f (S.toList.filter (fun v => R.f v ∈ grp i)) := by
    intro i hi hcoh
    simp only [hN, mem_filter, mem_Ico] at hi
    have hs := slotQ_spec R c i (by omega) (by omega)
    have h1 : Q.u i ∈ S.toList.filter (fun v => R.f v ∈ grp i) := by
      simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
      refine ⟨hs.1, ?_⟩
      rw [hs.2.2.1]; simp [hgrp]
    have h2 : Q.v i ∈ S.toList.filter (fun v => R.f v ∈ grp i) := by
      simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
      refine ⟨hs.2.1, ?_⟩
      rw [hs.2.2.2]; simp [hgrp]; right; exact hk.symm
    exact hi.2 (hcoh _ h1 _ h2)
  unfold realizedIncoherencyIndex incoherencyIndex realizedGroups
  rw [List.filter_map, List.length_map]
  have hnd := groups_nodup X R.k
  set p : List ℕ → Bool := fun g => decide (¬ GroupCoherent f (S.toList.filter (fun v => R.f v ∈ g))) with hp
  have hsub : N.image grp ⊆ ((X.expand R.k).groups.filter p).toFinset := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    have hi' := hi
    simp only [hN, mem_filter, mem_Ico] at hi'
    simp only [List.mem_toFinset, List.mem_filter]
    refine ⟨hmem i (by omega) (by omega), ?_⟩
    simp only [hp, decide_eq_true_eq]
    exact hbad i hi
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup (hnd.filter p)] at this
  exact this

end WaveTurbulence.LayerCnt
