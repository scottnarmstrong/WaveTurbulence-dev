/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Refinement
public import WaveTurbulence.Foundations.Cumulant.CoarseningWeight
import Mathlib.Logic.Equiv.Basic

/-!
# Cumulants of products

TARGET Lemma `propertycm` (`eqncm3`, L2343–L2351). The sum is over precisely the
source's irreducible partitions, with nonempty proper subfamilies excluded and
all product groups nonempty, as approved for unnormalized restricted measures.
-/

public section

namespace WaveTurbulence.CumulantProducts
open CumulantPartitions MeasureTheory
open scoped Classical

/-- Turn a sum over a predicate subtype into an ordinary indicator sum. -/
theorem sum_subtype_eq_sum_ite {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℂ) :
    (∑ a : {a // p a}, f a.1) = ∑ a : α, if p a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro a; simp) f, Finset.sum_filter]

/-- Interchange a weighted sum of refinement sums with a sum of coarse weights. -/
theorem sum_weighted_refinements {α ι : Type*} [Fintype α] [DecidableEq ι] {I : Finset ι}
    (G : α → Finpartition I) (w : α → ℂ) (V : Finpartition I → ℂ) :
    (∑ q : α, w q * ∑ R : {R : Finpartition I // R ≤ G q}, V R.1) =
      ∑ R : Finpartition I, V R * ∑ q : {q : α // R ≤ G q}, w q.1 := by
  simp_rw [sum_subtype_eq_sum_ite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

/-- Fine compatibility is refinement of the lifted group partition. -/
theorem respectsGroups_iff_le_groupPartition {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (P : Finpartition (I.biUnion S)) (Q : Finpartition I) :
    RespectsGroups S P Q ↔ P ≤ groupPartition I S hS hne Q := by
  constructor
  · intro h B hB
    obtain ⟨A, hA, hBA⟩ := h B hB
    exact ⟨A.biUnion S, Finset.mem_image.mpr ⟨A, hA, rfl⟩, hBA⟩
  · intro h B hB
    obtain ⟨C, hC, hBC⟩ := h hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨A, hA, hBC⟩

/-- A product over a lifted partition has one factor for every coarse block. -/
theorem prod_groupPartition {ι J M : Type*} [DecidableEq ι] [DecidableEq J] [CommMonoid M]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q : Finpartition I) (f : Finset J → M) :
    (∏ B ∈ (groupPartition I S hS hne Q).parts, f B) =
      ∏ A ∈ Q.parts, f (A.biUnion S) := by
  rw [groupPartition_parts]
  apply Finset.prod_image
  intro A hA B hB he
  exact biUnion_groups_injective hS hne (Q.le hA) (Q.le hB) he

/-- Rearrange a product over pairwise disjoint groups. -/
theorem prod_groups_eq_prod_biUnion {ι J M : Type*} [DecidableEq ι] [DecidableEq J]
    [CommMonoid M] {I : Finset ι} {S : ι → Finset J}
    (hS : (I : Set ι).PairwiseDisjoint S) {A : Finset ι} (hA : A ⊆ I) (f : J → M) :
    (∏ i ∈ A, ∏ j ∈ S i, f j) = ∏ j ∈ A.biUnion S, f j :=
  (Finset.prod_biUnion (fun _i hi _k hk hik => hS (hA hi) (hA hk) hik)).symm

/-- Moments of products are moments on the union of the groups. -/
theorem integral_prod_groups {Ω ι J : Type*} [MeasurableSpace Ω] [DecidableEq ι] [DecidableEq J]
    (μ : Measure Ω) (X : J → Ω → ℂ) {I : Finset ι} {S : ι → Finset J}
    (hS : (I : Set ι).PairwiseDisjoint S) {A : Finset ι} (hA : A ⊆ I) :
    (∫ ω, ∏ i ∈ A, ∏ j ∈ S i, X j ω ∂μ) = ∫ ω, ∏ j ∈ A.biUnion S, X j ω ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => prod_groups_eq_prod_biUnion hS hA (fun j => X j ω)

/-- Expand the block moments of products as a sum over fine refinements. -/
theorem prod_group_moments_eq_sum_refinements {Ω ι J : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq J] (μ : Measure Ω) (X : J → Ω → ℂ)
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q : Finpartition I) :
    (∏ A ∈ Q.parts, ∫ ω, ∏ i ∈ A, ∏ j ∈ S i, X j ω ∂μ) =
      ∑ P : {P : Finpartition (I.biUnion S) // P ≤ groupPartition I S hS hne Q},
        ∏ B ∈ P.1.parts, cumulant μ X B := by
  have h1 : (∏ A ∈ Q.parts, ∫ ω, ∏ i ∈ A, ∏ j ∈ S i, X j ω ∂μ) =
      ∏ A ∈ Q.parts, ∫ ω, ∏ j ∈ A.biUnion S, X j ω ∂μ :=
    Finset.prod_congr rfl (fun A hA => integral_prod_groups μ X hS (Q.le hA))
  rw [h1, ← prod_groupPartition I S hS hne Q
    (fun B : Finset J => ∫ ω, ∏ j ∈ B, X j ω ∂μ)]
  have h2 : (∏ B ∈ (groupPartition I S hS hne Q).parts, ∫ ω, ∏ j ∈ B, X j ω ∂μ) =
      ∏ B ∈ (groupPartition I S hS hne Q).parts, partitionExp (cumulant μ X) B := by
    apply Finset.prod_congr rfl
    intro B hB
    exact integral_prod_eq_sum_cumulant μ X B ((groupPartition I S hS hne Q).nonempty_of_mem_parts hB)
  rw [h2]
  exact prod_partitionExp_eq_sum_refinements _ _

end WaveTurbulence.CumulantProducts

namespace WaveTurbulence.CumulantProducts
open CumulantPartitions MeasureTheory
open scoped Classical

/-- The coefficient of a fine partition is its irreducibility indicator. -/
theorem sum_compatible_logWeight {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (hI : I.Nonempty) (P : Finpartition (I.biUnion S)) :
    (∑ Q : {Q : Finpartition I // P ≤ groupPartition I S hS hne Q}, logWeight Q.1.parts.card) =
      if IsIrreduciblePartition I S P then 1 else 0 := by
  have he (Q : Finpartition I) :
      P ≤ groupPartition I S hS hne Q ↔ groupComponentPartition S P ≤ Q :=
    (respectsGroups_iff_le_groupPartition I S hS hne P Q).symm.trans
      (groupComponentPartition_le_iff hS P Q).symm
  have h := Fintype.sum_equiv (Equiv.subtypeEquivRight he)
    (fun Q : {Q : Finpartition I // P ≤ groupPartition I S hS hne Q} => logWeight Q.1.parts.card)
    (fun Q : {Q : Finpartition I // groupComponentPartition S P ≤ Q} => logWeight Q.1.parts.card)
    (fun _ => rfl)
  rw [h, sum_coarsening_logWeight _ hI]
  simp only [← irreducible_iff_groupComponentPartition_eq_top hS hI P]

/-- TARGET Lemma `propertycm` for a nonempty family of nonempty disjoint groups.
All expectations are against the original measure, including when it is restricted to an event. -/
theorem cumulant_prod_nonempty {Ω ι J : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq J] (μ : Measure Ω) (X : J → Ω → ℂ)
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (hI : I.Nonempty) :
    cumulant μ (fun i ω => ∏ j ∈ S i, X j ω) I =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (I.biUnion S))).filter
        (IsIrreduciblePartition I S), ∏ B ∈ P.parts, cumulant μ X B := by
  change (∑ Q : Finpartition I, logWeight Q.parts.card *
    ∏ A ∈ Q.parts, ∫ ω, ∏ i ∈ A, ∏ j ∈ S i, X j ω ∂μ) = _
  have hm (Q : Finpartition I) := prod_group_moments_eq_sum_refinements μ X I S hS hne Q
  simp_rw [hm]
  rw [sum_weighted_refinements (fun Q : Finpartition I => groupPartition I S hS hne Q)
    (fun Q => logWeight Q.parts.card)
    (fun P => ∏ B ∈ P.parts, cumulant μ X B)]
  have hc (P : Finpartition (I.biUnion S)) := sum_compatible_logWeight I S hS hne hI P
  simp_rw [hc, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

end WaveTurbulence.CumulantProducts

namespace WaveTurbulence
open MeasureTheory
open scoped Classical

/-- Cumulants of products, TARGET Lemma `propertycm` (`eqncm3`, L2343–L2351).
The groups are pairwise disjoint and nonempty. Irreducibility excludes nonempty
proper subfamilies whose union is a union of partition blocks. The measure is
not normalized, so this applies directly to expectations against `P.restrict F`.
The formula is finite algebra in the totalized moments and needs no additional
integrability hypothesis. -/
theorem cumulant_prod {Ω ι J : Type*} [MeasurableSpace Ω] [DecidableEq ι] [DecidableEq J]
    (μ : Measure Ω) (X : J → Ω → ℂ) (I : Finset ι) (S : ι → Finset J)
    (hS : (I : Set ι).PairwiseDisjoint S) (hne : ∀ i ∈ I, (S i).Nonempty) :
    cumulant μ (fun i ω => ∏ j ∈ S i, X j ω) I =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (I.biUnion S))).filter
        (IsIrreduciblePartition I S), ∏ B ∈ P.parts, cumulant μ X B := by
  by_cases hI : I = ∅
  · subst I
    rw [cumulant_empty]
    have hirr (P : Finpartition ((∅ : Finset ι).biUnion S)) : IsIrreduciblePartition ∅ S P := by
      intro A hA hne _
      have he : A = ∅ := Finset.subset_empty.mp hA
      exact (hne.ne_empty he).elim
    have hf : (Finset.univ : Finset (Finpartition ((∅ : Finset ι).biUnion S))).filter
        (IsIrreduciblePartition ∅ S) = Finset.univ := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hirr]
    rw [hf]
    change (1 : ℂ) = CumulantPartitions.partitionExp (cumulant μ X) ((∅ : Finset ι).biUnion S)
    rw [Finset.biUnion_empty]
    exact (CumulantPartitions.partitionExp_empty (cumulant μ X)).symm
  · exact CumulantProducts.cumulant_prod_nonempty μ X I S hS hne
      (Finset.nonempty_iff_ne_empty.mpr hI)

end WaveTurbulence
