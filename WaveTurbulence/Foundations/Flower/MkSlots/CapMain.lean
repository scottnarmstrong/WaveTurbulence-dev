/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapFin
public import WaveTurbulence.Foundations.Flower.ProtPin.NTGate

/-! # B3s MK-SLOTS (cap slots): **`capSlotObligation : CapSlotObligation`**

The isolated cap-slot hypothesis of the integration (`IntCapHyp.lean`), proved:
* a trivial cap couple (two leaf trees) has a constant slot kernel of modulus `≤ 1` (`CapTriv`, `CapFin`), one
  centred mode;
* a nontrivial cap couple is D2b's paired tree `objTree` of the reconstruction with the `term` pin; its slot
  kernel is a unimodular constant times D3's admissible protected kernel (`CapNat`, `CapKerQ`, `CapMul*`), bounded
  by D3's proved `ProtPin.protBoundNTGate` (`CapD3`), turned into a superposition on the slot box (`CapSup`) and
  centred at the cap momentum (`CapCen`); the mass is compared with the B3 slot mass (`capMass_le`).

The constant: `capKc d η = capKcen d · max 1 (2 · capCsup d η)` (centring constant and main's Fourier
superposition constant at `θ = η`, `Λ = 30 d`). The prefix: D3's prefix with `η` also below `(γ₁/2)²` (so that
`√η + η⁸ ≤ γ₁`, comparing D3's incoherency gain `L^{-(γ₁-√η)g}` with `L^{-η⁸ g}`). -/

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

/-! ### The constants -/

/-- The centring constant (`cap_centre`). -/
def capKcen (d : ℕ) : ℝ := Classical.choose (cap_centre d)

theorem one_le_capKcen (d : ℕ) : 1 ≤ capKcen d := (Classical.choose_spec (cap_centre d)).1

/-- The Fourier superposition constant at `θ = η`, `Λ = 30 d` (`0` for `η < 0`). -/
def capCsup (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 0 ≤ η then Classical.choose (exists_capSupProp d h) else 0

theorem capCsup_ne_top (d : ℕ) (η : ℝ) : capCsup d η ≠ ⊤ := by
  unfold capCsup
  split_ifs with h
  · exact (Classical.choose_spec (exists_capSupProp d h)).1
  · exact ENNReal.zero_ne_top

theorem capCsup_spec (d : ℕ) {η : ℝ} (h : 0 ≤ η) : CapSupProp d η (capCsup d η) := by
  unfold capCsup
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_capSupProp d h)).2

/-! ### The mass comparison -/

theorem capRegBound_le (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (n g : ℕ) (hn : 1 ≤ n) :
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤
      (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
  have hC0 : 0 ≤ P.C₁ := le_trans zero_le_one hC1
  have hCC : 1 ≤ C := hC1.trans hC
  have h1 : (C * Real.sqrt P.δ) ^ (2 * n) = (C ^ 2) ^ n * P.δ ^ n := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hδ, mul_pow]
  have h2 : P.C₁ * (P.C₁ * P.δ) ^ n = P.C₁ ^ (n + 1) * P.δ ^ n := by
    rw [mul_pow, pow_succ]; ring
  have h3 : P.C₁ ^ (n + 1) ≤ (C ^ 2) ^ n := by
    calc P.C₁ ^ (n + 1) ≤ C ^ (n + 1) := pow_le_pow_left₀ hC0 hC _
      _ ≤ C ^ (2 * n) := pow_le_pow_right₀ hCC (by omega)
      _ = (C ^ 2) ^ n := pow_mul C 2 n
  have h4 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤ P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    nlinarith
  rw [h1, h2]
  have hδn : 0 ≤ P.δ ^ n := pow_nonneg hδ n
  have hLp : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc P.C₁ ^ (n + 1) * P.δ ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
      ≤ (C ^ 2) ^ n * P.δ ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by gcongr
    _ ≤ (C ^ 2) ^ n * P.δ ^ n * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by gcongr

/-! ### One cap pair -/

section Slot

variable {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

end Slot

end WaveTurbulence.Flower.MkSlots
