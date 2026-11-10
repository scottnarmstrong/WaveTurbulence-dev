/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMain

/-! # B3s MK-SLOTS (cap slots): **`capSlotObligation : CapSlotObligation`**

* `capSlot_triv_obl`: the trivial cap couple (one centred mode);
* `capSlotObligationAt_of`: one parameter record (D3's `ProtBoundNTAt`, `η` small against `γ₁`);
* **`capSlotObligation`**: the prefix, from D3's `ProtPin.protBoundNTGate`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign WaveTurbulence.Represents

namespace WaveTurbulence.Flower.MkSlots

section Slot

variable {P : WTParams} (hL : 2 ≤ P.L) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (C : ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (t s : ℝ)
  (hGeo : CapGeo (recLG a) J p)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

end Slot

/-! ### One parameter record -/

/-! ### The prefix -/

theorem sqrt_add_pow8_le {g η : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hη : 0 < η) (hηg : η ≤ (g / 2) ^ 2) :
    η ^ 8 ≤ g - Real.sqrt η := by
  have h1 : Real.sqrt η ≤ g / 2 := by
    calc Real.sqrt η ≤ Real.sqrt ((g / 2) ^ 2) := Real.sqrt_le_sqrt hηg
      _ = g / 2 := Real.sqrt_sq (by linarith)
  have hη1 : η ≤ 1 := hηg.trans (by nlinarith)
  have h2 : η ^ 8 ≤ η := pow_le_of_le_one hη.le hη1 (by norm_num)
  have h3 : (g / 2) ^ 2 ≤ g / 2 := by nlinarith
  linarith

end WaveTurbulence.Flower.MkSlots
