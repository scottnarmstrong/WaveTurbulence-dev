/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Basic
public import WaveTurbulence.Foundations.Cumulant.PartitionRecursion

/-!
# Moment–cumulant inversion

TARGET equation `eqncm2` (L571–L577). The proof is finite algebra: marking one
block gives the recurrence for the partition transforms, and the Möbius
coefficients cancel for every partition with more than one block. No
normalization of the measure or of the empty moment is used.
-/

public section

open scoped Classical
namespace WaveTurbulence.CumulantPartitions
/-- Möbius coefficient for a partition with `n` blocks. -/
@[expose] noncomputable def logWeight (n : ℕ) : ℂ := (-1 : ℂ) ^ (n - 1) * ((n - 1).factorial : ℂ)
/-- The finite logarithmic partition transform of a moment function. -/
@[expose] noncomputable def partitionLog {ι : Type*} [DecidableEq ι]
    (M : Finset ι → ℂ) (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, logWeight P.parts.card * ∏ A ∈ P.parts, M A

lemma logWeight_cancel (n : ℕ) (hn : 0 < n) :
    logWeight n + ((n - 1 : ℕ) : ℂ) * logWeight (n - 1) = if n = 1 then 1 else 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => norm_num [logWeight]
    | succ k =>
      rw [ite_eq_right (by omega)]
      have h1 : k.succ.succ - 1 = k + 1 := by omega
      simp only [logWeight, h1, Nat.add_sub_cancel, pow_succ, Nat.factorial_succ]
      push_cast
      ring

lemma marked_log_term {ι : Type*} [DecidableEq ι] {s B : Finset ι}
    (P : Finpartition s) (hB : B ∈ P.parts) (M : Finset ι → ℂ) :
    (logWeight (P.avoid B).parts.card * ∏ A ∈ (P.avoid B).parts, M A) * M B =
      logWeight (P.parts.card - 1) * ∏ A ∈ P.parts, M A := by
  rw [parts_avoid_block P hB, Finset.card_erase_of_mem hB, mul_assoc,
    Finset.prod_erase_mul _ _ hB]
end WaveTurbulence.CumulantPartitions

namespace WaveTurbulence.CumulantPartitions
lemma sum_partitionLog_complement {ι : Type*} [DecidableEq ι] (M : Finset ι → ℂ)
    (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (∑ B : SelectedBlock s (fun B => i ∉ B), partitionLog M (s \ B.1.1) * M B.1.1) =
      ∑ P : Finpartition s, ((P.parts.card - 1 : ℕ) : ℂ) *
        logWeight (P.parts.card - 1) * ∏ A ∈ P.parts, M A := by
  unfold partitionLog
  simp_rw [Finset.sum_mul]
  rw [sum_selected_complement_partitions s (fun B => i ∉ B)
    (fun B Q => (logWeight Q.parts.card * ∏ A ∈ Q.parts, M A) * M B)]
  apply Finset.sum_congr rfl
  intro P _
  have ht (B : {B : P.parts // i ∉ B.1}) := marked_log_term P B.1.property M
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [card_excluded_parts P i hi]
  ring

lemma partitionLog_recurrence {ι : Type*} [DecidableEq ι] (M : Finset ι → ℂ)
    (s : Finset ι) (i : ι) (hi : i ∈ s) :
    partitionLog M s +
      (∑ B : SelectedBlock s (fun B => i ∉ B), partitionLog M (s \ B.1.1) * M B.1.1) = M s := by
  rw [partitionLog, sum_partitionLog_complement M s i hi, ← Finset.sum_add_distrib]
  let P₀ : Finpartition s := Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩)
  rw [Finset.sum_eq_single P₀]
  · simp [P₀, logWeight]
  · intro P _ hne
    have hp : 0 < P.parts.card := Finset.card_pos.mpr
      (P.parts_nonempty (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩))
    have hn : P.parts.card ≠ 1 := fun h => hne (eq_indiscrete_of_card_parts_eq_one P ⟨i, hi⟩ h)
    have hw := logWeight_cancel P.parts.card hp
    rw [ite_eq_right hn] at hw
    linear_combination (∏ A ∈ P.parts, M A) * hw
  · intro h
    exact (h (Finset.mem_univ P₀)).elim

/-- The finite exponential partition transform. -/
@[expose] noncomputable def partitionExp {ι : Type*} [DecidableEq ι]
    (L : Finset ι → ℂ) (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, ∏ A ∈ P.parts, L A

lemma partitionExp_empty {ι : Type*} [DecidableEq ι] (L : Finset ι → ℂ) :
    partitionExp L ∅ = 1 := by
  unfold partitionExp
  have hp (P : Finpartition (∅ : Finset ι)) : P.parts = ∅ := P.parts_eq_empty_iff.mpr rfl
  simp only [hp, Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.cast_eq_one]
  exact Fintype.card_ofSubsingleton (Finpartition.empty (Finset ι))

lemma sum_partitionExp_complement {ι : Type*} [DecidableEq ι] (L : Finset ι → ℂ)
    (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (∑ A : SelectedBlock s (fun A => i ∈ A), L A.1.1 * partitionExp L (s \ A.1.1)) =
      partitionExp L s := by
  unfold partitionExp
  simp_rw [Finset.mul_sum]
  rw [sum_selected_complement_partitions s (fun A => i ∈ A)
    (fun A Q => L A * ∏ B ∈ Q.parts, L B)]
  apply Finset.sum_congr rfl
  intro P _
  have ht (B : {B : P.parts // i ∈ B.1}) :
      L B.1.1 * ∏ A ∈ (P.avoid B.1.1).parts, L A = ∏ A ∈ P.parts, L A := by
    rw [parts_avoid_block P B.1.property]
    exact Finset.mul_prod_erase P.parts L B.1.property
  simp_rw [ht]
  let B₀ : {B : P.parts // i ∈ B.1} := ⟨⟨P.part i, P.part_mem.mpr hi⟩, P.mem_part hi⟩
  have hall (B : {B : P.parts // i ∈ B.1}) : B = B₀ :=
    Subtype.ext (Subtype.ext (P.part_eq_of_mem B.1.property B.property).symm)
  apply Finset.sum_eq_single B₀
  · intro B _ hne
    exact (hne (hall B)).elim
  · intro h
    exact (h (Finset.mem_univ B₀)).elim

lemma partitionExp_recurrence {ι : Type*} [DecidableEq ι] (L : Finset ι → ℂ)
    (s : Finset ι) (i : ι) (hi : i ∈ s) :
    partitionExp L s = L s +
      ∑ B : SelectedBlock s (fun B => i ∉ B), L (s \ B.1.1) * partitionExp L B.1.1 := by
  rw [← sum_partitionExp_complement L s i hi]
  have h := Fintype.sum_equiv (complementBlockEquiv s i hi)
    (fun A : SelectedBlock s (fun A => i ∈ A) => L A.1.1 * partitionExp L (s \ A.1.1))
    (fun B : AvoidingSubset s i => L (s \ B.1.1) * partitionExp L B.1.1)
    (by
      intro A
      change L A.1.1 * partitionExp L (s \ A.1.1) =
        L (s \ (s \ A.1.1)) * partitionExp L (s \ A.1.1)
      rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp A.1.property)])
  rw [h, sum_avoidingSubset s i (fun B => L (s \ B) * partitionExp L B)]
  simp only [Finset.sdiff_empty, partitionExp_empty, mul_one]
end WaveTurbulence.CumulantPartitions

namespace WaveTurbulence.CumulantPartitions
lemma partitionExp_partitionLog {ι : Type*} [DecidableEq ι] (M : Finset ι → ℂ)
    (s : Finset ι) (hs : s.Nonempty) : partitionExp (partitionLog M) s = M s := by
  revert hs
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    obtain ⟨i, hi⟩ := hs
    calc
      _ = partitionLog M s + ∑ B : SelectedBlock s (fun B => i ∉ B),
          partitionLog M (s \ B.1.1) * partitionExp (partitionLog M) B.1.1 :=
        partitionExp_recurrence (partitionLog M) s i hi
      _ = partitionLog M s + ∑ B : SelectedBlock s (fun B => i ∉ B),
          partitionLog M (s \ B.1.1) * M B.1.1 := by
        apply congrArg (fun z : ℂ => partitionLog M s + z)
        apply Finset.sum_congr rfl
        intro B _
        have hBs := Finset.mem_powerset.mp B.1.property
        have hss : B.1.1 ⊂ s := lt_of_le_of_ne hBs
          (fun he => B.property.2 (he.symm ▸ hi))
        rw [ih _ hss B.property.1]
      _ = M s := partitionLog_recurrence M s i hi
end WaveTurbulence.CumulantPartitions

namespace WaveTurbulence
open MeasureTheory

/-- Moment–cumulant inversion, TARGET `eqncm2` (L571–L577), for a nonempty index set.
The finite identity is valid for an arbitrary measure, including `P.restrict F`.
Since it is algebraic in the individual moments, integrability is not needed for
this identity between the totalized Bochner integrals. -/
theorem integral_prod_eq_sum_cumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) (hs : s.Nonempty) :
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) =
      ∑ P : Finpartition s, ∏ A ∈ P.parts, cumulant μ X A := by
  have h := CumulantPartitions.partitionExp_partitionLog
    (fun A : Finset ι => ∫ ω, ∏ j ∈ A, X j ω ∂μ) s hs
  change (∑ P : Finpartition s, ∏ A ∈ P.parts, cumulant μ X A) =
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) at h
  exact h.symm

end WaveTurbulence

namespace WaveTurbulence.CumulantPartitions
lemma partitionExp_injective_nonempty {ι : Type*} [DecidableEq ι] (L K : Finset ι → ℂ)
    (h : ∀ s : Finset ι, s.Nonempty → partitionExp L s = partitionExp K s)
    (s : Finset ι) (hs : s.Nonempty) : L s = K s := by
  revert hs
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    obtain ⟨i, hi⟩ := hs
    have he := h s ⟨i, hi⟩
    rw [partitionExp_recurrence L s i hi, partitionExp_recurrence K s i hi] at he
    have hc : (∑ B : SelectedBlock s (fun B => i ∉ B),
        L (s \ B.1.1) * partitionExp L B.1.1) =
        ∑ B : SelectedBlock s (fun B => i ∉ B), K (s \ B.1.1) * partitionExp K B.1.1 := by
      apply Finset.sum_congr rfl
      intro B _
      have hsub : s \ B.1.1 ⊂ s := by
        apply lt_of_le_of_ne Finset.sdiff_subset
        intro heq
        obtain ⟨b, hb⟩ := B.property.1
        have hbs := Finset.mem_powerset.mp B.1.property hb
        have hc := Finset.mem_sdiff.mp (heq.symm ▸ hbs)
        exact hc.2 hb
      rw [ih _ hsub ⟨i, Finset.mem_sdiff.mpr ⟨hi, B.property.2⟩⟩, h _ B.property.1]
    rw [hc] at he
    exact add_right_cancel he

lemma partitionLog_partitionExp {ι : Type*} [DecidableEq ι] (L : Finset ι → ℂ)
    (s : Finset ι) (hs : s.Nonempty) : partitionLog (partitionExp L) s = L s :=
  partitionExp_injective_nonempty (partitionLog (partitionExp L)) L
    (fun t ht => partitionExp_partitionLog (partitionExp L) t ht) s hs
end WaveTurbulence.CumulantPartitions
