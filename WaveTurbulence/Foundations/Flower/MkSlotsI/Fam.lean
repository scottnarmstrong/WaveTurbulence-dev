/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CentreForm

/-! # B3s-HELPER7 (general assembly): the slot families from per-slot, per-centre superpositions

`GenSlotObligationAt` (revision 3) gives, for every outer slot `s'` of `G_sb` and every node centre `x`, a countable
superposition. Here these existentials become the data of the centre-indexed engine (`CentreForm`):

* `SlotDatum d`: one superposition (index type, weights, modes, centres, amplitudes, with the `SlotFam` bounds);
* `famOfData sd hsupp : SlotFam G d` (the family of the data at the centre `0`; leaf-pair localization `hsupp`);
* `chainPieceOf : SlotDatum d → ChainPiece d` (forget the centres) and `famCOfData sd` (the centred pieces);
* **`exists_slotData`**: from `∀ s' x, ∃ Λ … , Q s' x …` a choice `sd : ReplacementSlot G → (Fin d → ℤ) → SlotDatum d`
  with `Q` at every `(s', x)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-- One countable superposition with `SlotFam`-type bounds (centres `n` for leaf-pair localization). -/
structure SlotDatum (d : ℕ) where
  Λ : Type
  cnt : Countable Λ
  w : Λ → ℝ
  m : Λ → Fin 2 → ℤ
  n : Λ → Fin d → ℤ
  a : Λ → Mom d → ℂ
  w_nn : ∀ l, 0 ≤ w l
  w_sum : Summable w
  a_one : ∀ l k, ‖a l k‖ ≤ 1
  a_snorm : ∀ l, SNorm (30 * d) 0 (a l) ≤ 1

/-- The slot family of slot data (leaf-pair localization supplied). -/
def famOfData {G : Garden w} (sd : ReplacementSlot G → SlotDatum d)
    (hsupp : ∀ q l k, (sd (Sum.inl q)).a l k ≠ 0 → ‖k - latPt d ((sd (Sum.inl q)).n l)‖ ≤ 1) : SlotFam G d where
  Λ s := (sd s).Λ
  cnt s := (sd s).cnt
  w s := (sd s).w
  m s := (sd s).m
  n s := (sd s).n
  a s := (sd s).a
  w_nn s := (sd s).w_nn
  w_sum s := (sd s).w_sum
  a_one s := (sd s).a_one
  a_snorm s := (sd s).a_snorm
  a_supp := hsupp

/-- A slot datum as an (unlocalized) chain piece. -/
def chainPieceOf (D : SlotDatum d) : ChainPiece d where
  Λ := D.Λ
  cnt := D.cnt
  w := D.w
  m := D.m
  a := D.a
  w_nn := D.w_nn
  w_sum := D.w_sum
  a_one := D.a_one
  a_snorm := D.a_snorm

/-- The centred chain pieces of centre-indexed slot data. -/
def famCOfData {G : Garden w} (sd : ReplacementSlot G → (Fin d → ℤ) → SlotDatum d) :
    CentredSlot G → (Fin d → ℤ) → ChainPiece d :=
  fun c x => chainPieceOf (sd (Sum.inr c.1) x)

/-- **Choice of the slot data** from per-slot, per-centre existentials. -/
theorem exists_slotData {G : Garden w}
    (Q : ReplacementSlot G → (Fin d → ℤ) → (Λ : Type) → (Λ → ℝ) → (Λ → Fin 2 → ℤ) → (Λ → Fin d → ℤ) →
      (Λ → Mom d → ℂ) → Prop)
    (H : ∀ (s' : ReplacementSlot G) (x : Fin d → ℤ), ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ)
      (m : Λ → Fin 2 → ℤ) (c : Λ → Fin d → ℤ) (amp : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * d) 0 (amp l) ≤ 1) ∧
        Q s' x Λ wt m c amp) :
    ∃ sd : ReplacementSlot G → (Fin d → ℤ) → SlotDatum d,
      ∀ s' x, Q s' x (sd s' x).Λ (sd s' x).w (sd s' x).m (sd s' x).n (sd s' x).a := by
  choose Λ hcnt wt m c amp hw hsum ha hsn hQ using H
  exact ⟨fun s' x => ⟨Λ s' x, hcnt s' x, wt s' x, m s' x, c s' x, amp s' x, hw s' x, hsum s' x, ha s' x,
    hsn s' x⟩, fun s' x => hQ s' x⟩

end WaveTurbulence.Flower.MkSlotsI
