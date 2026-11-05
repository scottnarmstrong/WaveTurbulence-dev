/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PartitionConstructors

/-! # Literal enclosure of a partner involution between new first and last labels -/

@[expose] public section
namespace WaveTurbulence.Reg.PairPartition

/-- Pair the new outer endpoints and shift every old partner by one. -/
def enclosePartner {n : ℕ} (P : PairPartition n) : Fin (n+2) → Fin (n+2) :=
  Fin.cases (Fin.last (n+1)) (fun j => Fin.lastCases 0 (fun i => (P.pair i).castSucc.succ) j)

/-- Literal partner formula at the first endpoint. -/
theorem enclosePartner_zero {n : ℕ} (P : PairPartition n) : enclosePartner P 0 = Fin.last (n+1) := by
  simp [enclosePartner]

/-- Literal partner formula at the last endpoint. -/
theorem enclosePartner_last {n : ℕ} (P : PairPartition n) : enclosePartner P (Fin.last (n+1)) = 0 := by
  change enclosePartner P (Fin.last n).succ = 0
  rw [enclosePartner,Fin.cases_succ,Fin.lastCases_last]

/-- Literal partner formula at an interior shifted label. -/
theorem enclosePartner_inner {n : ℕ} (P : PairPartition n) (i : Fin n) :
    enclosePartner P i.castSucc.succ = (P.pair i).castSucc.succ := by
  simp [enclosePartner]

/-- The actual enclosed finite pair partition. -/
def enclose {n : ℕ} (P : PairPartition n) : PairPartition (n+2) where
  pair := enclosePartner P
  involutive := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [enclosePartner_zero,enclosePartner_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · change enclosePartner P (enclosePartner P (Fin.last (n+1))) = Fin.last (n+1)
        rw [enclosePartner_last,enclosePartner_zero]
      · rw [enclosePartner_inner,enclosePartner_inner,P.involutive]
  no_fixed := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [enclosePartner_zero]
      intro he
      have hv := congrArg Fin.val he
      change n+1 = 0 at hv
      omega
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · change enclosePartner P (Fin.last (n+1)) ≠ Fin.last (n+1)
        rw [enclosePartner_last]
        intro he
        have hv := congrArg Fin.val he
        change 0 = n+1 at hv
        omega
      · rw [enclosePartner_inner]
        intro he
        have hv := congrArg Fin.val he
        apply P.no_fixed k
        apply Fin.ext
        exact Nat.add_right_cancel hv

end WaveTurbulence.Reg.PairPartition
