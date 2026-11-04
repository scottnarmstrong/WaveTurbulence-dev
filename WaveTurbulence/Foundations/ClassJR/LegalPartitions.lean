/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Function.Basic

/-! # Noncrossing pair partitions (DH21 Definition 4.4, Proposition 4.5)

Labels are zero-based; the paper's label j corresponds to j - 1 here.

**Copied verbatim** from wt-resonant's REG-STRUCT scratch file
`/home/scott/wt-scratch/reg-struct/LegalPartitions.lean`, sha256
`91a6d0d27764c475f0951d84de60503696bd723d7319f3088622a57c08be1298`. The only changes are the
namespace (`WaveTurbulence.Reg` ↦ `WaveTurbulence.ClassJR`), the imports (the source imports
`WaveB2Draft.RegularDefs`, but the content needs only Mathlib) and this paragraph. After REG-STRUCT
lands, this file is replaced by the landed one, and `ChainPartition.lean` is re-pointed at it.
-/

@[expose] public section

namespace WaveTurbulence.ClassJR

/-- A partition of an ordered finite set into pairs, represented by its partner involution. -/
structure PairPartition (n : ℕ) where
  pair : Fin n → Fin n
  involutive : Function.Involutive pair
  no_fixed : ∀ a, pair a ≠ a

namespace PairPartition
variable {n : ℕ} (P : PairPartition n)

/-- DH21's legality condition: distinct pairs do not interlace. -/
def Legal : Prop := ∀ a b c d : Fin n, a < b → b < c → c < d →
  P.pair a = c → P.pair b = d → False

instance : Decidable P.Legal := by unfold Legal; infer_instance

theorem pair_injective : Function.Injective P.pair := P.involutive.injective

/-- The partner of a point strictly inside a legal pair stays strictly inside it. -/
theorem partner_inside (hP : P.Legal) {a b c : Fin n} (hab : P.pair a = b)
    (hac : a < c) (hcb : c < b) : a < P.pair c ∧ P.pair c < b := by
  have hba : P.pair b = a := by rw [← hab, P.involutive]
  have hna : P.pair c ≠ a := by
    intro he
    have h := congrArg P.pair he
    rw [P.involutive, hab] at h
    exact (ne_of_lt hcb) h
  have hnb : P.pair c ≠ b := by
    intro he
    exact (ne_of_gt hac) (P.pair_injective (he.trans hab.symm))
  constructor
  · by_contra h
    have hlt : P.pair c < a := lt_of_le_of_ne (le_of_not_gt h) hna
    exact hP (P.pair c) a c b hlt hac hcb (P.involutive c) hab
  · by_contra h
    have hlt : b < P.pair c := lt_of_le_of_ne (le_of_not_gt h) hnb.symm
    exact hP a c b (P.pair c) hac hcb hlt hab rfl

/-- Every nonempty legal interval contains an adjacent pair (DH21 Prop 4.5(1)). -/
theorem exists_adjacent_within (hP : P.Legal) {a b : Fin n}
    (hab : P.pair a = b) (hlt : a < b) :
    ∃ j k : Fin n, a ≤ j ∧ k ≤ b ∧ k.val = j.val + 1 ∧ P.pair j = k := by
  generalize hd : b.val - a.val = d
  induction d using Nat.strong_induction_on generalizing a b with
  | h d ih =>
    by_cases hadj : b.val = a.val + 1
    · exact ⟨a, b, le_rfl, le_rfl, hadj, hab⟩
    · let c : Fin n := ⟨a.val + 1, by have := b.isLt; change a.val < b.val at hlt; omega⟩
      have hac : a < c := by change a.val < a.val + 1; omega
      have hcb : c < b := by change a.val + 1 < b.val; change a.val < b.val at hlt; omega
      obtain ⟨hleft, hright⟩ := P.partner_inside hP hab hac hcb
      rcases lt_or_gt_of_ne (P.no_fixed c) with he | he
      · have hsmall : c.val - (P.pair c).val < d := by
          change a.val < (P.pair c).val at hleft
          change c.val < b.val at hcb
          have hc : c.val = a.val + 1 := rfl
          omega
        obtain ⟨j,k,hj,hk,hjk,hpair⟩ := ih _ hsmall (P.involutive c) he rfl
        exact ⟨j,k,(le_of_lt hleft).trans hj,hk.trans (le_of_lt hcb),hjk,hpair⟩
      · have hsmall : (P.pair c).val - c.val < d := by
          change (P.pair c).val < b.val at hright
          change a.val < c.val at hac
          omega
        obtain ⟨j,k,hj,hk,hjk,hpair⟩ := ih _ hsmall rfl he rfl
        exact ⟨j,k,(le_of_lt hac).trans hj,hk.trans (le_of_lt hright),hjk,hpair⟩

/-- Every nonempty legal partition has an adjacent pair to remove. -/
theorem exists_adjacent (hP : P.Legal) (hn : 0 < n) :
    ∃ j k : Fin n, k.val = j.val + 1 ∧ P.pair j = k := by
  let a : Fin n := ⟨0, hn⟩
  have hlt : a < P.pair a := by
    have hne : (P.pair a).val ≠ 0 := fun he => P.no_fixed a (Fin.ext he)
    change 0 < (P.pair a).val
    omega
  obtain ⟨j,k,_,_,hjk,hpair⟩ := P.exists_adjacent_within hP rfl hlt
  exact ⟨j,k,hjk,hpair⟩

end PairPartition
end WaveTurbulence.ClassJR
