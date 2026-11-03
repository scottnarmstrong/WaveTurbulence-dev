/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Coarsening

/-!
# Cancellation of cumulant coefficients over coarsenings

The coefficient sum vanishes unless the component partition has only one block.
-/

public section

namespace WaveTurbulence.CumulantProducts
open CumulantPartitions
open scoped Classical

/-- A partition whose every block is a singleton is the discrete partition. -/
theorem eq_bot_of_singleton_parts {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (P : Finpartition I) (h : ∀ A ∈ P.parts, A.card = 1) : P = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  obtain ⟨i, he⟩ := Finset.card_eq_one.mp (h A hA)
  have hi : i ∈ I := P.le hA (he.symm ▸ Finset.mem_singleton_self i)
  exact ⟨{i}, Finpartition.mem_bot_iff.mpr ⟨i, hi, rfl⟩, by rw [he]⟩

/-- The exponential partition transform of singleton weight is the constant one. -/
theorem partitionExp_singleton_weight {ι : Type*} [DecidableEq ι] (I : Finset ι) :
    partitionExp (fun A : Finset ι => if A.card = 1 then (1 : ℂ) else 0) I = 1 := by
  unfold partitionExp
  rw [Finset.sum_eq_single (⊥ : Finpartition I)]
  · simp [Finpartition.parts_bot]
  · intro P _ hP
    have hex : ∃ A ∈ P.parts, A.card ≠ 1 := by
      by_contra h
      push Not at h
      exact hP (eq_bot_of_singleton_parts P h)
    obtain ⟨A, hA, hcard⟩ := hex
    exact Finset.prod_eq_zero hA (ite_eq_right hcard)
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The logarithmic transform of constant moments is singleton weight. -/
theorem partitionLog_const_one {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty) :
    partitionLog (fun _ : Finset ι => (1 : ℂ)) I = if I.card = 1 then 1 else 0 := by
  have h := partitionLog_partitionExp (fun A : Finset ι => if A.card = 1 then (1 : ℂ) else 0) I hI
  have hE : partitionExp (fun A : Finset ι => if A.card = 1 then (1 : ℂ) else 0) =
      fun _ : Finset ι => (1 : ℂ) := funext partitionExp_singleton_weight
  rwa [hE] at h

/-- On a nonempty set, a partition has one block exactly when it is the top partition. -/
theorem card_parts_eq_one_iff_eq_top {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (hI : I.Nonempty) : R.parts.card = 1 ↔ R = ⊤ := by
  constructor
  · intro h
    have he := eq_indiscrete_of_card_parts_eq_one R hI h
    apply le_antisymm le_top
    intro A hA
    have hAI := Finset.mem_singleton.mp (Finpartition.parts_top_subset I hA)
    subst A
    refine ⟨I, ?_, le_rfl⟩
    rw [he, Finpartition.indiscrete_parts]
    exact Finset.mem_singleton_self I
  · rintro rfl
    have hlo : 0 < (⊤ : Finpartition I).parts.card := Finset.card_pos.mpr
      ((⊤ : Finpartition I).parts_nonempty (Finset.nonempty_iff_ne_empty.mp hI))
    have hhi := Finset.card_le_card (Finpartition.parts_top_subset I)
    simp only [Finset.card_singleton] at hhi
    omega

/-- Summing the Möbius cumulant coefficients over all coarsenings cancels every
partition with more than one component. -/
theorem sum_coarsening_logWeight {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (hI : I.Nonempty) :
    (∑ Q : {Q : Finpartition I // R ≤ Q}, logWeight Q.1.parts.card) =
      if R = ⊤ then 1 else 0 := by
  have h := Fintype.sum_equiv (coarseningEquiv R)
    (fun K : Finpartition (Finset.univ : Finset R.parts) => logWeight K.parts.card)
    (fun Q : {Q : Finpartition I // R ≤ Q} => logWeight Q.1.parts.card)
    (fun K => congrArg logWeight (coarseningLift_card R K).symm)
  rw [← h]
  have hne : (Finset.univ : Finset R.parts).Nonempty := by
    obtain ⟨A, hA⟩ := R.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hI)
    exact ⟨⟨A, hA⟩, Finset.mem_univ _⟩
  have hc := partitionLog_const_one (Finset.univ : Finset R.parts) hne
  simp only [partitionLog, Finset.prod_const_one, mul_one, Finset.card_univ, Fintype.card_coe] at hc
  rw [hc]
  simp only [card_parts_eq_one_iff_eq_top R hI]

end WaveTurbulence.CumulantProducts
