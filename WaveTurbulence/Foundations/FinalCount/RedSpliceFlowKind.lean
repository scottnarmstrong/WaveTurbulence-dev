/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
public import WaveTurbulence.Foundations.Spine.SourceVineData
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R25: gap norms of dart pairs of a block, of an ingredient and of the external pair

Generic facts for a molecule `M`, labels `k : D → E` with `k (mate x) = k x` and conservation at the atoms of
degree four (`∑ ζ k = 0`):
* `pair_norm_block`: an out/in pair of darts of a block `S` at one of its joints has gap norm `‖flow S a‖`.
* `pair_norm_ingredient`: the same for an out/in pair of an ingredient `A` of a chain `U` (flow equality).
* `ext_pair_norm`: an out/in pair at a joint of degree four of `S`, both darts NOT in `S`, has gap `= -flow`
  (the charge at a degree-four atom is zero), hence the same norm.
Gap kinds depend only on the norm (`gapKind_eq_of_norm_eq`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

section norm
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An out/in pair of a block at a joint: the gap norm is the norm of the flow at the first joint. -/
theorem pair_norm_block (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b j : V}
    (hB : M.IsBlock S a b) (hj : j = a ∨ j = b) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {x y : D} (hx : M.atom x = j) (hy : M.atom y = j) (hgx : M.InGroup S x) (hgy : M.InGroup S y)
    (hox : M.out x = true) (hoy : M.out y = false) :
    ‖k x - k y‖ = ‖groupFlow M S k a‖ := by
  have hgg : IsGroupGap M S k j (k x - k y) := ⟨x, y, hx, hy, hgx, hgy, hox, hoy, rfl⟩
  have hdeg := Mole.block_joint_degrees M hB
  rcases hj with rfl | rfl
  · rw [groupGap_eq_flow M hdeg.1 hgg]
  · rw [groupGap_eq_flow M hdeg.2 hgg]
    have := block_jointFlow_neg M hM hB k hk hc
    rw [this, norm_neg]

/-- The unordered version of `pair_norm_block`. -/
theorem pair_norm_block' (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b j : V}
    (hB : M.IsBlock S a b) (hj : j = a ∨ j = b) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {x y : D} (hx : M.atom x = j) (hy : M.atom y = j) (hgx : M.InGroup S x) (hgy : M.InGroup S y)
    (hne : M.out x ≠ M.out y) :
    ‖k x - k y‖ = ‖groupFlow M S k a‖ := by
  cases hox : M.out x
  · have hoy : M.out y = true := by
      cases h : M.out y
      · exact absurd (hox.trans h.symm) hne
      · rfl
    rw [norm_sub_rev]
    exact pair_norm_block M hM hB hj k hk hc hy hx hgy hgx hoy hox
  · have hoy : M.out y = false := by
      cases h : M.out y
      · rfl
      · exact absurd (hox.trans h.symm) hne
    exact pair_norm_block M hM hB hj k hk hc hx hy hgx hgy hox hoy

/-- The gap norm of an out/in pair of an ingredient `A` of a chain `U` at a joint of `A` is the norm of the flow
of the chain at its first joint. -/
theorem pair_norm_ingredient (M : Molecule V D) (hM : M.IsMolecule) {U A : Finset V} {a b x0 y0 j : V} {n : ℕ}
    (hI : ChainIngredient M U a b n A x0 y0) (hU : M.IsBlock U a b) (hj : j = x0 ∨ j = y0)
    (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {x y : D} (hx : M.atom x = j) (hy : M.atom y = j) (hgx : M.InGroup A x) (hgy : M.InGroup A y)
    (hne : M.out x ≠ M.out y) :
    ‖k x - k y‖ = ‖groupFlow M U k a‖ := by
  obtain ⟨_, ⟨X, hX⟩, _⟩ := chainIngredient_spec hI
  have h1 := pair_norm_block' M hM hX.1 hj k hk hc hx hy hgx hgy hne
  have h2 := (chainIngredient_flow_eq M hM k hk hc hI hU).1
  rw [h1, h2]

/-- The gap norm of an out/in pair of an ingredient at a joint of a block `S'` with the same atoms. -/
theorem flow_norm_joint (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b c d : V}
    (hB : M.IsBlock S a b) (hC : M.IsBlock S c d) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0) :
    ‖groupFlow M S k c‖ = ‖groupFlow M S k a‖ := by
  have hu := block_joints_unique M hB hC
  have hc' : c ∈ ({a, b} : Finset V) := by rw [hu]; exact mem_insert_self _ _
  rcases mem_insert.mp hc' with rfl | h
  · rfl
  · rw [mem_singleton] at h
    subst h
    rw [block_jointFlow_neg M hM hB k hk hc, norm_neg]

/-- **The external pair at a degree-four joint.** An out/in pair of darts at a joint `j` of the block `S`, neither
of which is in `S`, has gap equal to minus the internal flow, because the charge at a degree-four atom is zero. -/
theorem ext_pair_norm (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b j : V}
    (hB : M.IsBlock S a b) (hj : j = a ∨ j = b) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {d1 d2 : D} (h1 : M.atom d1 = j) (h2 : M.atom d2 = j) (hn1 : ¬ M.InGroup S d1) (hn2 : ¬ M.InGroup S d2)
    (ho1 : M.out d1 = true) (ho2 : M.out d2 = false) :
    ‖k d1 - k d2‖ = ‖groupFlow M S k a‖ := by
  classical
  have hjS : j ∈ S := by rcases hj with rfl | rfl; exact hB.2.1; exact hB.2.2.1
  have hjat : j ∈ M.atoms := hB.1 hjS
  have hdeg : M.degIn S j = 2 := by rcases hj with rfl | rfl; exact (Mole.block_joint_degrees M hB).1; exact (Mole.block_joint_degrees M hB).2
  have hne : d1 ≠ d2 := by intro h; rw [h] at ho1; rw [ho1] at ho2; cases ho2
  have hd1 : d1 ∈ (M.dartsAt j).filter (fun x => ¬ M.InGroup S x) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M j d1).mpr h1, hn1⟩
  have hd2 : d2 ∈ (M.dartsAt j).filter (fun x => ¬ M.InGroup S x) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M j d2).mpr h2, hn2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := M.dartsAt j) (fun x => M.InGroup S x)
  have hcard2 : 2 ≤ ((M.dartsAt j).filter (fun x => ¬ M.InGroup S x)).card := by
    have : ({d1, d2} : Finset D) ⊆ (M.dartsAt j).filter (fun x => ¬ M.InGroup S x) := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hd1
      · rw [mem_singleton.mp hz]; exact hd2
    have := card_le_card this
    rwa [card_pair hne] at this
  have h4 : M.deg j = 4 := by
    have hle := Mole.deg_le_four M hM hjat
    have : M.deg j = (M.dartsAt j).card := rfl
    have hdegIn : ((M.dartsAt j).filter (fun x => M.InGroup S x)).card = 2 := hdeg
    omega
  have hext : (M.dartsAt j).filter (fun x => ¬ M.InGroup S x) = {d1, d2} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hd1
      · rw [mem_singleton.mp hz]; exact hd2
    · have hdegIn : ((M.dartsAt j).filter (fun x => M.InGroup S x)).card = 2 := hdeg
      have : M.deg j = (M.dartsAt j).card := rfl
      have hc2 : ({d1, d2} : Finset D).card = 2 := card_pair hne
      omega
  have hsum := hc j hjat h4
  rw [← Finset.sum_filter_add_sum_filter_not (M.dartsAt j) (fun x => M.InGroup S x), hext,
    Finset.sum_pair hne] at hsum
  have e1 : M.dartSign d1 = 1 := by simp [Molecule.dartSign, ho1]
  have e2 : M.dartSign d2 = -1 := by simp [Molecule.dartSign, ho2]
  rw [e1, e2, one_smul, neg_one_smul] at hsum
  have hflow : groupFlow M S k j = -(k d1 - k d2) := by
    rw [sub_eq_add_neg]
    exact eq_neg_of_add_eq_zero_left hsum
  have hnorm : ‖k d1 - k d2‖ = ‖groupFlow M S k j‖ := by rw [hflow, norm_neg]
  rw [hnorm]
  rcases hj with rfl | rfl
  · rfl
  · rw [block_jointFlow_neg M hM hB k hk hc, norm_neg]

/-- The unordered version of `ext_pair_norm`. -/
theorem ext_pair_norm' (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b j : V}
    (hB : M.IsBlock S a b) (hj : j = a ∨ j = b) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {d1 d2 : D} (h1 : M.atom d1 = j) (h2 : M.atom d2 = j) (hn1 : ¬ M.InGroup S d1) (hn2 : ¬ M.InGroup S d2)
    (hne : M.out d1 ≠ M.out d2) :
    ‖k d1 - k d2‖ = ‖groupFlow M S k a‖ := by
  cases ho1 : M.out d1
  · have ho2 : M.out d2 = true := by
      cases h : M.out d2
      · exact absurd (ho1.trans h.symm) hne
      · rfl
    rw [norm_sub_rev]
    exact ext_pair_norm M hM hB hj k hk hc h2 h1 hn2 hn1 ho2 ho1
  · have ho2 : M.out d2 = false := by
      cases h : M.out d2
      · rfl
      · exact absurd (ho1.trans h.symm) hne
    exact ext_pair_norm M hM hB hj k hk hc h1 h2 hn1 hn2 ho1 ho2

/-- A vector whose norm is the norm of the flow at a joint has the gap kind of the block gap. -/
theorem kind_of_flow_norm (M : Molecule V D) {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {r z : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hz : ‖z‖ = ‖groupFlow M S (Molecule.kvec L w κ) a‖) :
    Molecule.gapKind L γ η z = Molecule.gapKind L γ η r := by
  have : r = groupFlow M S (Molecule.kvec L w κ) a := groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr
  rw [this] at *
  exact gapKind_eq_of_norm_eq L γ η hz

end norm

end WaveTurbulence.RedSplice
