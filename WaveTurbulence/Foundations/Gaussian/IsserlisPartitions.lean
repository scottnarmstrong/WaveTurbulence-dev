/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.IsserlisPairings
public import Mathlib.Order.Partition.Finpartition

/-!
# Pairings as partitions into opposite-sign pairs

Correspondence between the bijection representation and the set partitions
used in DH21 Lemma A.2.
-/

public section

namespace WaveTurbulence.GaussianPairings

open scoped Classical

/-- The two-element blocks associated to an opposite-sign pairing. -/
@[expose] noncomputable def pairingParts {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) : Finset (Finset J) :=
  Finset.univ.image fun a : SignedPositions s ζ true => {a.1.1, (e a).1.1}

private theorem positive_ne_negative {J : Type*} {s : Finset J} {ζ : J → Bool}
    (a : SignedPositions s ζ true) (b : SignedPositions s ζ false) : a.1.1 ≠ b.1.1 := by
  intro h
  have hh := congrArg ζ h
  rw [a.property, b.property] at hh
  exact Bool.noConfusion hh

/-- A positive position belongs to exactly the pair indexed by itself. -/
theorem positive_mem_pair_iff {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) (a p : SignedPositions s ζ true) :
    a.1.1 ∈ ({p.1.1, (e p).1.1} : Finset J) ↔ a = p := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Subtype.ext (Subtype.ext h)
    · exact (positive_ne_negative a (e p) h).elim
  · rintro rfl
    exact Or.inl rfl

/-- A negative position belongs to exactly the pair indexed by its inverse image. -/
theorem negative_mem_pair_iff {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) (b : SignedPositions s ζ false) (p : SignedPositions s ζ true) :
    b.1.1 ∈ ({p.1.1, (e p).1.1} : Finset J) ↔ b = e p := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (positive_ne_negative p b h.symm).elim
    · exact Subtype.ext (Subtype.ext h)
  · rintro rfl
    exact Or.inr rfl

theorem pairingParts_existsUnique {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) (j : J) (hj : j ∈ s) :
    ∃! B, B ∈ pairingParts e ∧ j ∈ B := by
  cases hz : ζ j with
  | true =>
    let a : SignedPositions s ζ true := ⟨⟨j, hj⟩, hz⟩
    refine ⟨{a.1.1, (e a).1.1}, ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩,
      Finset.mem_insert_self _ _⟩, ?_⟩
    intro B hB
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hB.1
    have ha : a = p := (positive_mem_pair_iff e a p).mp hB.2
    rw [← ha]
  | false =>
    let b : SignedPositions s ζ false := ⟨⟨j, hj⟩, hz⟩
    refine ⟨{(e.symm b).1.1, b.1.1}, ⟨?_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨e.symm b, Finset.mem_univ _, by rw [e.apply_symm_apply]⟩
    · intro B hB
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hB.1
      have hb : b = e p := (negative_mem_pair_iff e b p).mp hB.2
      rw [hb, e.symm_apply_apply]

/-- The source set partition associated with a bijection pairing. -/
@[expose] noncomputable def pairingPartition {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) : Finpartition s :=
  Finpartition.ofExistsUnique (pairingParts e)
    (by
      intro B hB
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hB
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact a.1.property
      · rw [Finset.mem_singleton] at hj
        exact hj ▸ (e a).1.property)
    (pairingParts_existsUnique e)
    (by
      intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      exact Finset.nonempty_iff_ne_empty.mp (Finset.insert_nonempty _ _) ha)

end WaveTurbulence.GaussianPairings

namespace WaveTurbulence.GaussianPairings
open scoped Classical

/-- A partition of the source kind: every block is one positive and one negative position. -/
@[expose] def IsOppositeSignPartition {J : Type*} {s : Finset J} (ζ : J → Bool)
    (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, ∃ a : SignedPositions s ζ true, ∃ b : SignedPositions s ζ false,
    B = {a.1.1, b.1.1}

/-- Every bijection pairing gives a partition into opposite-sign pairs. -/
theorem pairingPartition_isOppositeSign {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) : IsOppositeSignPartition ζ (pairingPartition e) := by
  intro B hB
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨a, e a, rfl⟩

private theorem negative_partner_unique {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (a : SignedPositions s ζ true) (b c : SignedPositions s ζ false)
    (hb : {a.1.1, b.1.1} ∈ P.parts) (hc : {a.1.1, c.1.1} ∈ P.parts) : b = c := by
  have he : ({a.1.1, b.1.1} : Finset J) = {a.1.1, c.1.1} :=
    (P.part_eq_of_mem hb (Finset.mem_insert_self _ _)).symm.trans
      (P.part_eq_of_mem hc (Finset.mem_insert_self _ _))
  have hm : b.1.1 ∈ ({a.1.1, c.1.1} : Finset J) := by rw [← he]; simp
  rcases Finset.mem_insert.mp hm with h | h
  · exact (positive_ne_negative a b h.symm).elim
  · exact Subtype.ext (Subtype.ext (Finset.mem_singleton.mp h))

private theorem positive_partner_unique {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (a c : SignedPositions s ζ true) (b : SignedPositions s ζ false)
    (ha : {a.1.1, b.1.1} ∈ P.parts) (hc : {c.1.1, b.1.1} ∈ P.parts) : a = c := by
  have he : ({a.1.1, b.1.1} : Finset J) = {c.1.1, b.1.1} :=
    (P.part_eq_of_mem (a := b.1.1) ha (by simp)).symm.trans
      (P.part_eq_of_mem (a := b.1.1) hc (by simp))
  have hm : a.1.1 ∈ ({c.1.1, b.1.1} : Finset J) := by rw [← he]; simp
  rcases Finset.mem_insert.mp hm with h | h
  · exact Subtype.ext (Subtype.ext h)
  · exact (positive_ne_negative a b (Finset.mem_singleton.mp h)).elim

/-- Each positive position in a source pairing has exactly one negative partner. -/
theorem existsUnique_negative_partner {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (hP : IsOppositeSignPartition ζ P) (a : SignedPositions s ζ true) :
    ∃! b : SignedPositions s ζ false, {a.1.1, b.1.1} ∈ P.parts := by
  obtain ⟨p, b, he⟩ := hP (P.part a.1.1) (P.part_mem.mpr a.1.property)
  have hm := P.mem_part a.1.property
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  have ha : a = p := by
    rcases hm with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact (positive_ne_negative a b h).elim
  subst p
  have hb : {a.1.1, b.1.1} ∈ P.parts := he ▸ P.part_mem.mpr a.1.property
  exact ⟨b, hb, fun c hc => negative_partner_unique P a c b hc hb⟩

/-- Each negative position in a source pairing has exactly one positive partner. -/
theorem existsUnique_positive_partner {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (hP : IsOppositeSignPartition ζ P) (b : SignedPositions s ζ false) :
    ∃! a : SignedPositions s ζ true, {a.1.1, b.1.1} ∈ P.parts := by
  obtain ⟨a, q, he⟩ := hP (P.part b.1.1) (P.part_mem.mpr b.1.property)
  have hm := P.mem_part b.1.property
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  have hb : b = q := by
    rcases hm with h | h
    · exact (positive_ne_negative a b h.symm).elim
    · exact Subtype.ext (Subtype.ext h)
  subst q
  have ha : {a.1.1, b.1.1} ∈ P.parts := he ▸ P.part_mem.mpr b.1.property
  exact ⟨a, ha, fun c hc => positive_partner_unique P c a b hc ha⟩

end WaveTurbulence.GaussianPairings

namespace WaveTurbulence.GaussianPairings
open scoped Classical

/-- The bijection obtained by taking the unique opposite-sign partner in each source block. -/
@[expose] noncomputable def pairingOfPartition {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (hP : IsOppositeSignPartition ζ P) : SignedPairing s ζ where
  toFun a := Classical.choose (existsUnique_negative_partner P hP a).exists
  invFun b := Classical.choose (existsUnique_positive_partner P hP b).exists
  left_inv a := by
    apply (existsUnique_positive_partner P hP
      (Classical.choose (existsUnique_negative_partner P hP a).exists)).unique
    · exact Classical.choose_spec (existsUnique_positive_partner P hP _).exists
    · exact Classical.choose_spec (existsUnique_negative_partner P hP a).exists
  right_inv b := by
    apply (existsUnique_negative_partner P hP
      (Classical.choose (existsUnique_positive_partner P hP b).exists)).unique
    · exact Classical.choose_spec (existsUnique_negative_partner P hP _).exists
    · exact Classical.choose_spec (existsUnique_positive_partner P hP b).exists

/-- The selected partner lies in the same two-element source block. -/
theorem pairingOfPartition_mem {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (hP : IsOppositeSignPartition ζ P) (a : SignedPositions s ζ true) :
    {a.1.1, (pairingOfPartition P hP a).1.1} ∈ P.parts :=
  Classical.choose_spec (existsUnique_negative_partner P hP a).exists

/-- Passing from a source pair partition to a bijection and back preserves the partition. -/
theorem pairingPartition_pairingOfPartition {J : Type*} {s : Finset J} {ζ : J → Bool}
    (P : Finpartition s) (hP : IsOppositeSignPartition ζ P) :
    pairingPartition (pairingOfPartition P hP) = P := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hB
    exact pairingOfPartition_mem P hP a
  · intro hB
    obtain ⟨a, b, rfl⟩ := hP B hB
    have hb : pairingOfPartition P hP a = b :=
      (existsUnique_negative_partner P hP a).unique (pairingOfPartition_mem P hP a) hB
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by rw [hb]⟩

/-- Passing from a bijection to its source pair partition and back preserves the bijection. -/
theorem pairingOfPartition_pairingPartition {J : Type*} {s : Finset J} {ζ : J → Bool}
    (e : SignedPairing s ζ) :
    pairingOfPartition (pairingPartition e) (pairingPartition_isOppositeSign e) = e := by
  apply Equiv.ext
  intro a
  apply (existsUnique_negative_partner (pairingPartition e) (pairingPartition_isOppositeSign e) a).unique
  · exact pairingOfPartition_mem _ _ a
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- The bijection carrier for DH21 Lemma A.2 is equivalent to its source carrier:
partitions of the positions into opposite-sign two-element blocks. -/
@[expose] noncomputable def signedPairingEquivFinpartition {J : Type*} (s : Finset J) (ζ : J → Bool) :
    SignedPairing s ζ ≃ {P : Finpartition s // IsOppositeSignPartition ζ P} where
  toFun e := ⟨pairingPartition e, pairingPartition_isOppositeSign e⟩
  invFun P := pairingOfPartition P.1 P.2
  left_inv e := pairingOfPartition_pairingPartition e
  right_inv P := Subtype.ext (pairingPartition_pairingOfPartition P.1 P.2)

end WaveTurbulence.GaussianPairings

namespace WaveTurbulence.GaussianPairings
open scoped Classical

/-- A product over the source partition is the product over its positive positions,
with each unordered pair counted exactly once. -/
theorem prod_pairingPartition_parts {J M : Type*} [CommMonoid M]
    {s : Finset J} {ζ : J → Bool} (e : SignedPairing s ζ) (w : Finset J → M) :
    (∏ B ∈ (pairingPartition e).parts, w B) =
      ∏ a : SignedPositions s ζ true, w {a.1.1, (e a).1.1} := by
  change (∏ B ∈ Finset.univ.image (fun a : SignedPositions s ζ true =>
    ({a.1.1, (e a).1.1} : Finset J)), w B) = _
  apply Finset.prod_image
  intro a _ b _ hab
  change ({a.1.1, (e a).1.1} : Finset J) = {b.1.1, (e b).1.1} at hab
  apply (positive_mem_pair_iff e a b).mp
  rw [← hab]
  exact Finset.mem_insert_self _ _

end WaveTurbulence.GaussianPairings
