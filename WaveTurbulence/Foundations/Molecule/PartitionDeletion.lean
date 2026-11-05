/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LegalPartitions

/-! # Removing and reinserting an adjacent pair (DH21 Proposition 4.5(1))

Surviving labels keep their order. The increasing enumeration of the complement
is the zero-based version of the paper's explicit shift by two.
-/

@[expose] public section

namespace WaveTurbulence.Reg
namespace PairPartition

variable {n k : ℕ} (P : PairPartition n)

/-- Restrict a partner involution to the image of an increasing embedding. -/
noncomputable def restrict (e : Fin k ↪o Fin n)
    (hc : ∀ i, ∃ j, e j = P.pair (e i)) : PairPartition k where
  pair i := Classical.choose (hc i)
  involutive i := by
    apply e.injective
    rw [Classical.choose_spec (hc _), Classical.choose_spec (hc i), P.involutive]
  no_fixed i hi := by
    have he := Classical.choose_spec (hc i)
    rw [hi] at he
    exact P.no_fixed (e i) he.symm

/-- Restriction retains the actual partner map. -/
theorem restrict_pair (e : Fin k ↪o Fin n) (hc : ∀ i, ∃ j, e j = P.pair (e i)) (i) :
    e ((P.restrict e hc).pair i) = P.pair (e i) := Classical.choose_spec (hc i)

/-- Increasing restriction preserves noncrossing. -/
theorem restrict_legal (hP : P.Legal) (e : Fin k ↪o Fin n)
    (hc : ∀ i, ∃ j, e j = P.pair (e i)) : (P.restrict e hc).Legal := by
  intro a b c d hab hbc hcd hac hbd
  apply hP (e a) (e b) (e c) (e d) (e.strictMono hab) (e.strictMono hbc) (e.strictMono hcd)
  · rw [← P.restrict_pair e hc, hac]
  · rw [← P.restrict_pair e hc, hbd]

/-- Labels remaining after removal of two paired endpoints. -/
def remaining (a b : Fin n) : Finset (Fin n) := (Finset.univ.erase a).erase b

/-- Increasing enumeration of the labels remaining after deletion. -/
noncomputable def remainingEmbedding (a b : Fin n) : Fin (remaining a b).card ↪o Fin n :=
  (Finset.orderIsoOfFin (remaining a b) rfl).toOrderEmbedding.trans (OrderEmbedding.subtype _)

theorem remainingEmbedding_mem (a b : Fin n) (i) :
    remainingEmbedding a b i ∈ remaining a b :=
  (Finset.orderIsoOfFin (remaining a b) rfl i).2

theorem remaining_closed {a b : Fin n} (hab : P.pair a = b) :
    ∀ i, ∃ j, remainingEmbedding a b j = P.pair (remainingEmbedding a b i) := by
  intro i
  have hi := remainingEmbedding_mem a b i
  simp only [remaining, Finset.mem_erase, Finset.mem_univ, and_true] at hi
  have hba : P.pair b = a := by rw [← hab, P.involutive]
  have hn₁ : P.pair (remainingEmbedding a b i) ≠ b :=
    fun h => hi.2 (P.pair_injective (h.trans hab.symm))
  have hn₂ : P.pair (remainingEmbedding a b i) ≠ a :=
    fun h => hi.1 (P.pair_injective (h.trans hba.symm))
  let y : remaining a b := ⟨P.pair (remainingEmbedding a b i), by
    simp only [remaining, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hn₁, hn₂⟩⟩
  exact ⟨(Finset.orderIsoOfFin (remaining a b) rfl).symm y,
    congrArg Subtype.val ((Finset.orderIsoOfFin (remaining a b) rfl).apply_symm_apply y)⟩

/-- Actual deletion of one pair, with the original order retained. -/
noncomputable def deletePair {a b : Fin n} (hab : P.pair a = b) :
    PairPartition (remaining a b).card :=
  P.restrict (remainingEmbedding a b) (P.remaining_closed hab)

/-- Removing a pair reduces the cardinality by exactly two. -/
theorem remaining_card {a b : Fin n} (hab : P.pair a = b) :
    (remaining a b).card + 2 = n := by
  have hne : b ≠ a := hab ▸ P.no_fixed a
  have hb : b ∈ Finset.univ.erase a := by simp [hne]
  have ha := Finset.card_erase_add_one (Finset.mem_univ a)
  have hh := Finset.card_erase_add_one hb
  simp only [Finset.card_univ, Fintype.card_fin] at ha
  change ((Finset.univ.erase a).erase b).card + 2 = n
  omega

/-- Deletion preserves legality. -/
theorem deletePair_legal (hP : P.Legal) {a b : Fin n} (hab : P.pair a = b) :
    (P.deletePair hab).Legal := P.restrict_legal hP _ _

/-- A pair with a strictly intermediate label cannot meet an adjacent pair. -/
theorem endpoints_outside_adjacent {a b x y z : Fin n} (hab : P.pair a = b)
    (hadj : b.val = a.val + 1) (hxy : P.pair x = y) (hxz : x < z) (hzy : z < y) :
    x ∈ remaining a b ∧ y ∈ remaining a b := by
  have hba : P.pair b = a := by rw [← hab, P.involutive]
  have hxyv : x.val + 1 < y.val := by
    change x.val < z.val at hxz
    change z.val < y.val at hzy
    omega
  have hx₁ : x ≠ a := by
    intro he
    have hy : y = b := hxy.symm.trans (he ▸ hab)
    have hvx := congrArg Fin.val he
    have hvy := congrArg Fin.val hy
    omega
  have hx₂ : x ≠ b := by
    intro he
    have hy : y = a := hxy.symm.trans (he ▸ hba)
    have hvx := congrArg Fin.val he
    have hvy := congrArg Fin.val hy
    omega
  have hy₁ : y ≠ a := by
    intro he
    have hx : x = b := by
      have hh := congrArg P.pair (hxy.trans he)
      rw [P.involutive, hab] at hh
      exact hh
    have hvx := congrArg Fin.val hx
    have hvy := congrArg Fin.val he
    omega
  have hy₂ : y ≠ b := by
    intro he
    have hx : x = a := by
      have hh := congrArg P.pair (hxy.trans he)
      rw [P.involutive, hba] at hh
      exact hh
    have hvx := congrArg Fin.val hx
    have hvy := congrArg Fin.val he
    omega
  simp only [remaining, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨⟨hx₂, hx₁⟩, ⟨hy₂, hy₁⟩⟩

/-- Reinserting an adjacent pair preserves legality; no crossing can use that pair. -/
theorem legal_of_deletePair {a b : Fin n} (hab : P.pair a = b)
    (hadj : b.val = a.val + 1) (hP : (P.deletePair hab).Legal) : P.Legal := by
  intro x y z t hxy hyz hzt hxz hyt
  obtain ⟨hx,hz⟩ := P.endpoints_outside_adjacent hab hadj hxz hxy hyz
  obtain ⟨hy,ht⟩ := P.endpoints_outside_adjacent hab hadj hyt hyz hzt
  let e := Finset.orderIsoOfFin (remaining a b) rfl
  let X := e.symm ⟨x,hx⟩
  let Y := e.symm ⟨y,hy⟩
  let Z := e.symm ⟨z,hz⟩
  let T := e.symm ⟨t,ht⟩
  have hex : remainingEmbedding a b X = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  have hey : remainingEmbedding a b Y = y := congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
  have hez : remainingEmbedding a b Z = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
  have het : remainingEmbedding a b T = t := congrArg Subtype.val (e.apply_symm_apply ⟨t,ht⟩)
  have hpX : (P.deletePair hab).pair X = Z := by
    apply (remainingEmbedding a b).injective
    rw [deletePair, P.restrict_pair, hex, hxz, hez]
  have hpY : (P.deletePair hab).pair Y = T := by
    apply (remainingEmbedding a b).injective
    rw [deletePair, P.restrict_pair, hey, hyt, het]
  apply hP X Y Z T _ _ _ hpX hpY
  · exact e.symm.strictMono hxy
  · exact e.symm.strictMono hyz
  · exact e.symm.strictMono hzt

/-- DH21 Prop 4.5(1), deletion/insertion equivalence for any adjacent pair. -/
theorem legal_iff_deletePair {a b : Fin n} (hab : P.pair a = b)
    (hadj : b.val = a.val + 1) : P.Legal ↔ (P.deletePair hab).Legal :=
  ⟨fun h => P.deletePair_legal h hab, P.legal_of_deletePair hab hadj⟩

end PairPartition
end WaveTurbulence.Reg
