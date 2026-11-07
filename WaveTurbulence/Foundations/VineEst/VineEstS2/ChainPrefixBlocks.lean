/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CurrentBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockConcatenation
public import WaveTurbulence.Foundations.Molecule.MoleculeOrientationGroups

/-! # Actual source-chain prefixes are current connected blocks -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open Finset RegRed
variable {V D : Type*} [DecidableEq V] [Fintype D]

theorem chain_joints_ne {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M S a b n) : a ≠ b := by
  cases h with
  | single h => obtain ⟨X,hX⟩ := h; exact hX.1.2.2.2.1
  | append _ _ _ hne => exact hne

theorem chain_atoms_subset {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M S a b n) : S ⊆ M.atoms := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact hX.1.1
  | append _ hT _ _ ih => obtain ⟨X,hX⟩ := hT; exact union_subset ih hX.1.1

omit [Fintype D] in
theorem currentGroupConnected_union (M : Molecule V D) {S T : Finset V} {b : V}
    (hS : M.GroupConnected S) (hT : M.GroupConnected T) (hbS : b ∈ S) (hbT : b ∈ T) :
    M.GroupConnected (S ∪ T) := by
  have lift (A B : Finset V) (hAB : A ⊆ B) {u v : V}
      (hp : Relation.EqvGen (fun p q => ∃ x, M.InGroup A x ∧ M.atom x = p ∧ M.atom (M.mate x) = q) u v) :
      Relation.EqvGen (fun p q => ∃ x, M.InGroup B x ∧ M.atom x = p ∧ M.atom (M.mate x) = q) u v := by
    apply Relation.EqvGen.mono (fun _ _ h => ?_) u v hp
    obtain ⟨x,hx,hp,hq⟩ := h
    exact ⟨x,⟨hAB hx.1,hAB hx.2⟩,hp,hq⟩
  intro u hu v hv
  have toB (x : V) (hx : x ∈ S ∪ T) :
      Relation.EqvGen (fun p q => ∃ e, M.InGroup (S ∪ T) e ∧ M.atom e = p ∧ M.atom (M.mate e) = q) x b := by
    rcases mem_union.mp hx with hx | hx
    · exact lift S (S ∪ T) subset_union_left (hS x hx b hbS)
    · exact lift T (S ∪ T) subset_union_right (hT x hx b hbT)
  exact Relation.EqvGen.trans _ _ _ (toB u hu) (Relation.EqvGen.symm _ _ (toB v hv))

theorem chain_current_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M S a b n) : M.GroupConnected S := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ := hX.1
    exact hc
  | @append S T a b c n hS hT _ _ ih =>
    obtain ⟨X,hX⟩ := hT
    have hcT : M.GroupConnected T := by
      obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ := hX.1
      exact hc
    exact currentGroupConnected_union M ih hcT (Vine.chain_joints_mem hS).2 hX.1.2.1

theorem chain_endpoint_lower {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    obtain ⟨_,_,_,_,hoa,hia,hob,hib,_,_⟩ := hX.1
    omega
  | @append S T a b c n _ hT _ _ ih =>
    obtain ⟨X,hX⟩ := hT
    have ho := Mole.outIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
    have hi := Mole.inIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
    have hoc := Mole.outIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
    have hic := Mole.inIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
    obtain ⟨_,_,_,_,_,_,hot,hit,_,_⟩ := hX.1
    omega

/-- The shared singleton contains no bond, because an actual connected vine
has no loop at either joint. -/
theorem chain_append_intersection_degree {M : Molecule V D} {S T : Finset V} {b c : V}
    {X : VineType} (hT : M.IsVine X T b c) (hi : S ∩ T = {b}) : M.degIn (S ∩ T) b = 0 := by
  have hd := (isBlock_iff_degree_connected _ _ _ _).mp hT.1
  rw [hi]
  apply Mole.degIn_singleton_eq_zero M
  intro x hx
  have h := Mole.connected_block_no_joint_loop M hT.1 hd.2 (Or.inl hx)
  simpa only [hx] using h

/-- Every non-endpoint of the actual chain saturates its four ambient
incidences; no prefix-block assumption is needed. -/
theorem chain_interior_degree (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Vine.Chain M S a b n) :
    ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    exact ((isBlock_iff_degree_connected _ _ _ _).mp hX.1).1.2.2.2.2.2.2.2.2
  | @append S T a b c n hS hT hi _ ih =>
    obtain ⟨X,hX⟩ := hT
    have hdT := ((isBlock_iff_degree_connected _ _ _ _).mp hX.1).1
    intro v hv hva hvc
    have hvM := (union_subset (chain_atoms_subset hS) hdT.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v = b
    · subst v
      have hlo := chain_endpoint_lower hS
      have hsum := Mole.outIn_add_inIn M S b
      have hdegT := (Mole.block_joint_degrees M hX.1).1
      have hadd := Mole.degIn_union_add_inter M S T (Vine.chain_joints_mem hS).2 hdT.2.1
      rw [chain_append_intersection_degree hX hi] at hadd
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hm := Mole.degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hdT.2.2.2.2.2.2.2.2 v hv hvb hvc
        have hm := Mole.degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- The defining source VC block premise gives a current connected prefix
block. All degrees and connectivity are proved from the actual chain. -/
theorem chain_prefix_currentBlock (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : Vine.Chain M S a b n)
    {X : VineType} (hT : M.IsVine X T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hlo := chain_endpoint_lower hS
  have hmem := Vine.chain_joints_mem hS
  have hdegT := ((isBlock_iff_degree_connected _ _ _ _).mp hT.1).1
  have hdegU := ((isBlock_iff_degree_connected _ _ _ _).mp hU).1
  have huaout := hdegU.2.2.2.2.1
  have huain := hdegU.2.2.2.2.2.1
  have hbU : b ∈ S ∪ T := mem_union_left _ hmem.2
  have hb4 := hdegU.2.2.2.2.2.2.2.2 b hbU (Ne.symm (chain_joints_ne hS)) hdegT.2.2.2.1
  have hadd := Mole.degIn_union_add_inter M S T hmem.2 hdegT.2.1
  rw [chain_append_intersection_degree hT hi] at hadd
  have hb2 := (Mole.block_joint_degrees M hT.1).1
  have hsum := Mole.outIn_add_inIn M S b
  have hoa := Mole.outIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hia := Mole.inIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
  refine (isBlock_iff_degree_connected M S a b).mpr ⟨?_,?_⟩
  · refine ⟨chain_atoms_subset hS,hmem.1,hmem.2,chain_joints_ne hS,?_,?_,?_,?_,chain_interior_degree M hM hS⟩ <;> omega
  · exact (groupConnected_iff_mole M S ⟨a,hmem.1⟩).mp (chain_current_connected hS)

end WaveTurbulence.VineEstS2
