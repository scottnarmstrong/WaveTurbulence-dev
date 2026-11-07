/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Export

/-! The READY total-couple export replaces the former partial Y6 interface. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open FlowerP7 LGSpine

abbrev P7PostedInput : Prop := type_of% @FlowerP7.coupleSum_total_bound

theorem p7PostedInput : P7PostedInput := @FlowerP7.coupleSum_total_bound

/-- Full couple clause, with the owner's numerical and regular-family premises explicit. -/
theorem couple_clause_bound_of_p7 (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Set.Ioo (p : ℝ) (p + 1)) (k : Mom P.d)
    (kind : TreeKind) (dt : Bool) (hkdt : kind = .tr → dt = true)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * (N : ℝ)) :=
  FlowerP7.coupleSum_total_bound C₀ P G hp Rr hRr hR1 hN ht k kind dt hkdt hγ hGN hCN H hE

end WaveTurbulence.FlowerTop
