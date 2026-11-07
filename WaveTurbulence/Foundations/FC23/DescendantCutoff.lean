/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerSlices
/-! The T1/T2 split and the auxiliary cutoff on native descendant carriers. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset
variable {w d : ℕ}

def directTopNodes (LG : LayeredGarden w) (p : ℕ) (j : Fin w) : Finset (GNode LG.garden.tree) :=
  univ.filter fun a => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a ∧ LG.layer a = p

def attachedTopNodes (LG : LayeredGarden w) (p : ℕ) (j : Fin w) : Finset (GNode LG.garden.tree) :=
  univ.filter fun a => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a ∧ LG.layer a < p

theorem topNodes_partition (LG : LayeredGarden w) (p : ℕ) (hc : IsCanonH (p + 1) LG)
    (j : Fin w) :
    (univ.filter fun a : GNode LG.garden.tree => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a) =
      directTopNodes LG p j ∪ attachedTopNodes LG p j := by
  ext a
  have ha := Canon.layer_le_of_isCanonH hc a
  simp only [directTopNodes, attachedTopNodes, mem_union, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rcases Nat.lt_or_eq_of_le ha with hlt | heq
    · exact Or.inr ⟨h.1, h.2.1, h.2.2, hlt⟩
    · exact Or.inl ⟨h.1, h.2.1, h.2.2, heq⟩
  · rintro (h | h) <;> exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem topNodes_disjoint (LG : LayeredGarden w) (p : ℕ) (j : Fin w) :
    Disjoint (directTopNodes LG p j) (attachedTopNodes LG p j) := by
  rw [disjoint_left]
  intro a ha hb
  have he := (mem_filter.mp ha).2.2.2.2
  have hl := (mem_filter.mp hb).2.2.2.2
  omega

/-- Exact T1/T2 decomposition on the frozen original-tree top carrier. -/
theorem native_T1_T2 (LG : LayeredGarden w) (p : ℕ) (hc : IsCanonH (p + 1) LG)
    (j : Fin w) (L : ℝ) (r : ℕ) (k : GNode LG.garden.tree → Mom d) :
    prodDyadicCut L (r + 1)
      (univ.filter fun a : GNode LG.garden.tree => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a)
      (fun a => ‖k a‖) =
      ((∏ a ∈ directTopNodes LG p j, chi0 (‖k a‖ / (2 ^ (r + 1) * L))) -
        ∏ a ∈ directTopNodes LG p j, chi0 (‖k a‖ / (2 ^ r * L))) *
        (∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (2 ^ (r + 1) * L))) +
      (∏ a ∈ directTopNodes LG p j, chi0 (‖k a‖ / (2 ^ r * L))) *
        ((∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (2 ^ (r + 1) * L))) -
          ∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (2 ^ r * L))) := by
  rw [topNodes_partition LG p hc j]
  simp only [prodDyadicCut, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel]
  rw [prod_union (topNodes_disjoint LG p j), prod_union (topNodes_disjoint LG p j)]
  ring

/-- A lower node in a canonical flower garden has no flower descendant. -/
theorem lower_descendants_free {LG : LayeredGarden w} {p : ℕ}
    (hc : IsCanonH (p + 1) LG) (a : GNode LG.garden.tree) (ha : LG.layer a < p) :
    a.leavesBelow ⊆ freeTreeLeaves LG a.1.1 := by
  intro l hl
  have hd := (mem_filter.mp hl).2
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hd.1.symm⟩
  intro hf
  have he := hc.2.1 a ⟨l, hf, hd⟩
  omega

/-- Conservation on the actual descendant carrier forces a large endpoint;
the endpoint can have either sign. -/
theorem descendant_large_leaf {LG : LayeredGarden w} (k : GNode LG.garden.tree → Mom d)
    (hk : IsDecoration LG.garden k) (a : GNode LG.garden.tree) {A : ℝ}
    (hlarge : (a.leavesBelow.card : ℝ) * A < ‖k a‖) :
    ∃ l ∈ a.leavesBelow, A < ‖k l.toNode‖ := by
  by_contra hn
  push Not at hn
  have he := Comb.sum_rule LG.garden.sig k hk.1 a
  have hsum : ‖k a‖ ≤ ∑ l ∈ a.leavesBelow, ‖k l.toNode‖ := by
    calc
      ‖k a‖ = ‖((nodeSign LG.garden.sig a.1 : ℤˣ) : ℤ) • k a‖ :=
        (norm_isUnit_zsmul _ (nodeSign LG.garden.sig a.1).isUnit).symm
      _ = ‖∑ l ∈ a.leavesBelow, ((nodeSign LG.garden.sig l.1 : ℤˣ) : ℤ) • k l.toNode‖ := congrArg norm he
      _ ≤ ∑ l ∈ a.leavesBelow, ‖((nodeSign LG.garden.sig l.1 : ℤˣ) : ℤ) • k l.toNode‖ := norm_sum_le _ _
      _ = _ := sum_congr rfl fun l _ => norm_isUnit_zsmul _ (nodeSign LG.garden.sig l.1).isUnit
  have hb : (∑ l ∈ a.leavesBelow, ‖k l.toNode‖) ≤ (a.leavesBelow.card : ℝ) * A := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (s := a.leavesBelow) hn
  exact (not_lt_of_ge (hsum.trans hb)) hlarge

/-- Actual auxiliary cutoff: a large attached bond annihilates the product
of cutoffs on all nonflower endpoints of its original tree. -/
theorem native_auxiliary_cutoff {LG : LayeredGarden w} {p : ℕ} (hc : IsCanonH (p + 1) LG)
    (k : GNode LG.garden.tree → Mom d) (hk : IsDecoration LG.garden k)
    (a : GNode LG.garden.tree) (ha : LG.layer a < p) {A : ℝ} (hA : 0 < A)
    (hlarge : ((freeTreeLeaves LG a.1.1).card : ℝ) * A < ‖k a‖) (T : ℝ) :
    T = T * (1 - ∏ l ∈ freeTreeLeaves LG a.1.1, chi0 (‖k l.toNode‖ / A)) := by
  have hsub := lower_descendants_free hc a ha
  have hcard : (a.leavesBelow.card : ℝ) ≤ (freeTreeLeaves LG a.1.1).card := by
    exact_mod_cast card_le_card hsub
  obtain ⟨l, hl, hnorm⟩ := descendant_large_leaf k hk a
    ((mul_le_mul_of_nonneg_right hcard hA.le).trans_lt hlarge)
  have hz : chi0 (‖k l.toNode‖ / A) = 0 := by
    rw [frozen_chi0_eq]
    apply Fourier.chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hA.le)]
    exact (one_le_div hA).mpr hnorm.le
  rw [prod_eq_zero (hsub hl) hz, sub_zero, mul_one]

/-- Nonzero bond difference supplies the required large attached bond. -/
theorem bond_difference_large (LG : LayeredGarden w) (p : ℕ) (j : Fin w)
    (k : GNode LG.garden.tree → Mom d) {M : ℝ} (hM : 0 < M)
    (hneq : (∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / M)) -
      (∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (M / 2))) ≠ 0) :
    ∃ a ∈ attachedTopNodes LG p j, M / 4 < ‖k a‖ := by
  by_contra hn
  push Not at hn
  have hcut (a : GNode LG.garden.tree) (ha : a ∈ attachedTopNodes LG p j) :
      chi0 (‖k a‖ / M) = 1 ∧ chi0 (‖k a‖ / (M / 2)) = 1 := by
    have hnorm := hn a ha
    constructor <;> rw [frozen_chi0_eq] <;> apply Fourier.chi0_eq_one
    · rw [abs_of_nonneg (by positivity), div_le_iff₀ hM]
      linarith
    · rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity : 0 < M / 2)]
      linarith
  apply hneq
  rw [prod_eq_one (fun a ha => (hcut a ha).1), prod_eq_one (fun a ha => (hcut a ha).2), sub_self]

/-- The T2 term can be multiplied by the auxiliary tail, with no extra
hypothesis on the decoration beyond native conservation and pairing. -/
theorem native_T2_auxiliary {LG : LayeredGarden w} {p : ℕ} (hc : IsCanonH (p + 1) LG)
    (j : Fin w) (k : GNode LG.garden.tree → Mom d) (hk : IsDecoration LG.garden k)
    {M A : ℝ} (hM : 0 < M) (hA : 0 < A)
    (hscale : ((freeTreeLeaves LG j).card : ℝ) * A ≤ M / 4) :
    let T := (∏ a ∈ directTopNodes LG p j, chi0 (‖k a‖ / (M / 2))) *
      ((∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / M)) -
        ∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (M / 2)))
    T = T * (1 - ∏ l ∈ freeTreeLeaves LG j, chi0 (‖k l.toNode‖ / A)) := by
  dsimp only
  by_cases hz : (∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / M)) -
      (∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / (M / 2))) = 0
  · rw [hz, mul_zero, zero_mul]
  · obtain ⟨a, ha, hlarge⟩ := bond_difference_large LG p j k hM hz
    have hj := (mem_filter.mp ha).2.1
    have hl := (mem_filter.mp ha).2.2.2.2
    have he := native_auxiliary_cutoff hc k hk a hl hA
      (by rw [hj]; exact hscale.trans_lt hlarge)
    rw [hj] at he
    exact he _
end WaveTurbulence.FC23
