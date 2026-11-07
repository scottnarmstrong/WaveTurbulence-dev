/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.AdapterFalse
/-! FLOWER-P7 EXPORT: the total couple bound, in the shape of FS9's `couple_clause_bound`, over LG-SPINE's gates. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

/-- **`coupleSum` bound for every admissible `(kind, dt)`** (`kind = tr → dt = true`), by decapitation:
`‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{ν N}` (even `δ^{2νN}`).
It replaces both `RegularCouplesAt` and `CoupleStage1At` inside `couple_clause_bound`: the regular/nonregular split
does not factor over the components of the decapitation (a nonregular couple can decapitate into three regular
couples), so the TOTAL sum is bounded, regular components by the family bound of FLOWER-REG
(`regular_family_pointwise2`, two-time port) and the nonregular ones by LG-SPINE's slice estimates. -/
theorem coupleSum_total_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Set.Ioo (p : ℝ) (p + 1)) (k : Mom P.d)
    (kind : TreeKind) (dt : Bool) (hkdt : kind = .tr → dt = true)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * (N : ℝ)) := by
  have hδ0 := G.hs.delta_pos
  have hδ1 := G.hs.delta_le
  have hν := G.hs.nu_pos.le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow : P.δ ^ (2 * P.ν * (N : ℝ)) ≤ P.δ ^ (P.ν * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by nlinarith)
  have hj : 0 ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _) (Real.rpow_nonneg (by linarith [G.hs.L_ge]) _)
  have key : ‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
    cases dt with
    | true => exact coupleSum_true_total C₀ P G hp Rr hRr hR1 hN ⟨ht.1.le, ht.2.le⟩ k kind hγ hGN hCN H hE
    | false =>
      have hk : kind = .L0 := by
        cases kind with
        | tr => exact absurd (hkdt rfl) (by simp)
        | L0 => rfl
      subst hk
      exact coupleSum_false_total C₀ P G hp Rr hRr hR1 hN t k hγ hGN hCN H hE
  exact key.trans (mul_le_mul_of_nonneg_left hpow hj)

end WaveTurbulence.FlowerP7
