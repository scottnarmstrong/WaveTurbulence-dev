/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Inversion
public import WaveTurbulence.Foundations.Gaussian.IsserlisMoments
public import WaveTurbulence.Foundations.Gaussian.IsserlisPartitions

/-!
# Gaussian cumulants

The complex Isserlis formula is the partition exponential of the pair
covariance. Moment–cumulant inversion therefore leaves precisely that quadratic
term. The vanishing assertion is restricted to nonempty sets, since the literal
TARGET definition assigns the empty cumulant the value one.
-/

public section

open MeasureTheory ProbabilityTheory
open WaveTurbulence.GaussianPairings
open scoped Classical

namespace WaveTurbulence

/-- A two-element opposite-sign block on which the Gaussian labels agree. -/
@[expose] def IsGaussianPairBlock {J ι : Type*} [DecidableEq J] (k : J → ι) (ζ : J → Bool) (A : Finset J) : Prop :=
  (∃ a b : J, A = {a, b} ∧ ζ a = true ∧ ζ b = false) ∧
    ∀ a ∈ A, ∀ b ∈ A, k a = k b

/-- The pair covariance, viewed as a function on finite sets of positions. -/
@[expose] noncomputable def gaussianPairWeight {J ι : Type*} [DecidableEq J] (k : J → ι)
    (ζ : J → Bool) (A : Finset J) : ℂ := if IsGaussianPairBlock k ζ A then 1 else 0

/-- Exponentiating an indicator weight counts the partitions whose blocks satisfy it. -/
theorem partitionExp_indicator {J : Type*} [DecidableEq J] (p : Finset J → Prop)
    [DecidablePred p] (s : Finset J) :
    CumulantPartitions.partitionExp (fun A => if p A then (1 : ℂ) else 0) s =
      (Nat.card {P : Finpartition s // ∀ A ∈ P.parts, p A} : ℂ) := by
  unfold CumulantPartitions.partitionExp
  simp only [Finset.prod_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem pairingPartition_gaussian_iff {J ι : Type*} [DecidableEq J] {s : Finset J}
    (k : J → ι) (ζ : J → Bool) (e : SignedPairing s ζ) :
    (∀ A ∈ (pairingPartition e).parts, IsGaussianPairBlock k ζ A) ↔
      ∀ a : SignedPositions s ζ true, k (e a).1 = k a.1 := by
  constructor
  · intro h a
    have hb := h {a.1.1, (e a).1.1} (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    exact hb.2 _ (by simp) _ (by simp)
  · intro h A hA
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
    refine ⟨⟨a.1.1, (e a).1.1, rfl, a.property, (e a).property⟩, ?_⟩
    intro j hj l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hl
    rcases hj with rfl | rfl <;> rcases hl with rfl | rfl
    · rfl
    · exact (h a).symm
    · exact h a
    · rfl

theorem isOppositeSign_of_gaussian_blocks {J ι : Type*} [DecidableEq J] {s : Finset J}
    (k : J → ι) (ζ : J → Bool) (P : Finpartition s)
    (hP : ∀ A ∈ P.parts, IsGaussianPairBlock k ζ A) : IsOppositeSignPartition ζ P := by
  intro A hA
  obtain ⟨⟨a, b, he, ha, hb⟩, _⟩ := hP A hA
  refine ⟨⟨⟨a, P.le hA ?_⟩, ha⟩, ⟨⟨b, P.le hA ?_⟩, hb⟩, he⟩ <;> rw [he] <;> simp

/-- Label-preserving pairing bijections are exactly the partitions into Gaussian pair blocks. -/
@[expose] noncomputable def gaussianPairingEquivPartition {J ι : Type*} [DecidableEq J]
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    {e : SignedPairing s ζ // ∀ a : SignedPositions s ζ true, k (e a).1 = k a.1} ≃
      {P : Finpartition s // ∀ A ∈ P.parts, IsGaussianPairBlock k ζ A} where
  toFun e := ⟨pairingPartition e.1, (pairingPartition_gaussian_iff k ζ e.1).mpr e.2⟩
  invFun P := ⟨pairingOfPartition P.1 (isOppositeSign_of_gaussian_blocks k ζ P.1 P.2), by
    apply (pairingPartition_gaussian_iff k ζ _).mp
    rw [pairingPartition_pairingOfPartition]
    exact P.2⟩
  left_inv e := Subtype.ext (pairingOfPartition_pairingPartition e.1)
  right_inv P := Subtype.ext (pairingPartition_pairingOfPartition P.1
    (isOppositeSign_of_gaussian_blocks k ζ P.1 P.2))

/-- Isserlis moments are the partition exponential of the pair covariance. -/
theorem integral_signed_prod_eq_partitionExp {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    (∫ ω, ∏ j ∈ s, if ζ j then η (k j) ω else star (η (k j) ω) ∂P) =
      CumulantPartitions.partitionExp (gaussianPairWeight k ζ) s := by
  rw [integral_signed_prod_eq_prod_factorial hη hlaw]
  have hc := card_compatible_signedPairing s k ζ
  have he : (∀ e : SignedPairing s ζ,
      (∀ a, positionLabel s k ζ false (e a) = positionLabel s k ζ true a) ↔
        ∀ a : SignedPositions s ζ true, k (e a).1 = k a.1) := by
    intro e
    simp only [positionLabel, Subtype.mk.injEq]
  have hcard := Nat.card_congr (gaussianPairingEquivPartition s k ζ)
  change _ = CumulantPartitions.partitionExp
    (fun A => if IsGaussianPairBlock k ζ A then (1 : ℂ) else 0) s
  rw [partitionExp_indicator]
  rw [← hcard]
  simp_rw [he] at hc
  rw [hc]
  push_cast
  rfl

end WaveTurbulence

namespace WaveTurbulence

/-- Gaussian cumulants are exactly the pair covariance, for nonempty sets of factors
(TARGET `defcm`, using DH21 Lemma A.2). -/
theorem cumulant_signed_eq_gaussianPairWeight {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (hs : s.Nonempty) (k : J → ι) (ζ : J → Bool) :
    cumulant P (fun j ω => if ζ j then η (k j) ω else star (η (k j) ω)) s =
      gaussianPairWeight k ζ s := by
  change CumulantPartitions.partitionLog
    (fun A : Finset J => ∫ ω, ∏ j ∈ A,
      if ζ j then η (k j) ω else star (η (k j) ω) ∂P) s = _
  have hM : (fun A : Finset J => ∫ ω, ∏ j ∈ A,
      if ζ j then η (k j) ω else star (η (k j) ω) ∂P) =
      CumulantPartitions.partitionExp (gaussianPairWeight k ζ) :=
    funext fun A => integral_signed_prod_eq_partitionExp hη hlaw A k ζ
  rw [hM]
  exact CumulantPartitions.partitionLog_partitionExp (gaussianPairWeight k ζ) s hs

/-- Every Gaussian pair block has exactly two elements. -/
theorem IsGaussianPairBlock.card_eq_two {J ι : Type*} [DecidableEq J]
    {k : J → ι} {ζ : J → Bool} {A : Finset J} (h : IsGaussianPairBlock k ζ A) : A.card = 2 := by
  obtain ⟨⟨a, b, rfl, ha, hb⟩, _⟩ := h
  have hab : a ≠ b := by
    intro he
    have hh := congrArg ζ he
    rw [ha, hb] at hh
    exact Bool.noConfusion hh
  exact Finset.card_pair hab

/-- A Gaussian cumulant of nonzero order vanishes unless its order is two. -/
theorem cumulant_signed_eq_zero_of_card_ne_two {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (hs : s.Nonempty) (k : J → ι) (ζ : J → Bool) (hcard : s.card ≠ 2) :
    cumulant P (fun j ω => if ζ j then η (k j) ω else star (η (k j) ω)) s = 0 := by
  rw [cumulant_signed_eq_gaussianPairWeight hη hlaw s hs k ζ]
  exact ite_eq_right (fun h => hcard h.card_eq_two)

/-- A Gaussian cumulant vanishes when the factors do not form an opposite-sign pair. -/
theorem cumulant_signed_eq_zero_of_no_opposite_pair {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (hs : s.Nonempty) (k : J → ι) (ζ : J → Bool)
    (hshape : ¬∃ a b : J, s = {a, b} ∧ ζ a = true ∧ ζ b = false) :
    cumulant P (fun j ω => if ζ j then η (k j) ω else star (η (k j) ω)) s = 0 := by
  rw [cumulant_signed_eq_gaussianPairWeight hη hlaw s hs k ζ]
  exact ite_eq_right (fun h => hshape h.1)

/-- For an opposite-sign pair, the Gaussian cumulant is the index-equality indicator. -/
theorem cumulant_signed_pair {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (k : J → ι) (ζ : J → Bool) (a b : J) (ha : ζ a = true) (hb : ζ b = false) :
    cumulant P (fun j ω => if ζ j then η (k j) ω else star (η (k j) ω)) {a, b} =
      if k a = k b then 1 else 0 := by
  rw [cumulant_signed_eq_gaussianPairWeight hη hlaw {a, b} (Finset.insert_nonempty _ _) k ζ]
  have he : IsGaussianPairBlock k ζ {a, b} ↔ k a = k b := by
    constructor
    · intro h
      exact h.2 a (by simp) b (by simp)
    · intro h
      refine ⟨⟨a, b, rfl, ha, hb⟩, ?_⟩
      intro j hj l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj hl
      rcases hj with rfl | rfl <;> rcases hl with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
  simp only [gaussianPairWeight, he]

end WaveTurbulence
