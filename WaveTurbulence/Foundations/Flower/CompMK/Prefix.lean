/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.NonReg
public import WaveTurbulence.Foundations.Flower.CompMK.Mono
public import WaveTurbulence.Foundations.Flower.FinalMKCrude.Gate
public import WaveTurbulence.Foundations.Flower.FinalMKFine.Gate
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Prefix

/-! # C5b COMP-MK: the non-regular part under the flower prefix

`nonregPrefix`: from B4's gate `WTPrefix (Stage1ReductionAtMKSel C₀ cP cθ)` and D7's input `SelSumTargetT`, with the
three READY marked gates (C2 `coarseSplicedGateMK`, C4b `fineSplicedGateHalfMK`, C4a `ladderFourierMKFace_prefix`),
`WTPrefixP (NonregComponentBoundAtI 17999)` for `1 ≤ C₀`, `0 ≤ cP ≤ 500`, `1 ≤ cθ`.

The prefix conditions: main's `prefix_with_stage1_small` (`PieceSmall`, `FinalAbsorptionAt (6C₀)`), and three
eventual choices made here: `δ ≤ cθ^{-40}` (so `cθ^{40ν}δ^ν ≤ 1`), `L ≥ e^{Pm+1}` (so `log L ≥ 1` and
`2Pm ≤ 10·R_{p+1}`), and `(log L)^K + 1 ≤ L` (so `N_{p+1}^4 + 1 ≤ L`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory Filter
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

/-- `(log L)^K + 1 ≤ L` eventually. -/
theorem exists_log_pow_add_one_le (K : ℕ) : ∃ L₁ : ℝ, 2 ≤ L₁ ∧ ∀ L, L₁ ≤ L → Real.log L ^ K + 1 ≤ L := by
  have hb := (Real.isLittleO_pow_log_id_atTop (n := K)).bound (c := 1 / 2) (by norm_num)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 hb
  refine ⟨max L₀ 2, le_max_right _ _, fun L hL => ?_⟩
  have h1 := hL₀ L ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have h2 : Real.log L ^ K ≤ ‖Real.log L ^ K‖ := Real.le_norm_self _
  have h3 : ‖(id L : ℝ)‖ = L := by simp [abs_of_pos (by linarith : (0 : ℝ) < L)]
  rw [h3] at h1
  linarith

/-- `R_D = ⌊(log L)^{40d}⌋ ≥ Pm` once `log L ≥ Pm + 1`, and `R_{D-k}` only grows with `k`. -/
theorem le_R_of_log (P : WTParams) (hd : 1 ≤ P.d) {Pm : ℕ} (hlog : (Pm : ℝ) + 1 ≤ Real.log P.L) (q : ℕ) :
    Pm ≤ P.R q := by
  have h0 : Pm + 1 ≤ P.Rdown 0 := by
    simp only [WTParams.Rdown]
    refine Nat.le_floor ?_
    have hl1 : 1 ≤ Real.log P.L := by have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _; linarith
    have : Real.log P.L ≤ Real.log P.L ^ (40 * P.d) := le_self_pow₀ hl1 (by omega)
    push_cast
    linarith
  have hmono : ∀ k, Pm + 1 ≤ P.Rdown k := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      simp only [WTParams.Rdown]
      have h1 : P.Rdown k ≤ P.Rdown k ^ (40 * P.d) := Nat.le_self_pow (by omega) _
      have h2 : P.Rdown k ^ (40 * P.d) ≤ (P.Rdown k ^ (40 * P.d)) ^ (40 * P.d) := Nat.le_self_pow (by omega) _
      omega
  have := hmono (P.D - q)
  simp only [WTParams.R]
  omega

/-- `cθ^{40ν}δ^ν ≤ 1` for `δ ≤ cθ^{-40}`. -/
theorem ctheta_delta_le {cθ δ ν : ℝ} (hcθ : 1 ≤ cθ) (hδ0 : 0 < δ) (hδ : δ ≤ (cθ ^ 40)⁻¹) (hν : 0 ≤ ν) :
    cθ ^ (40 * ν) * δ ^ ν ≤ 1 := by
  have hc0 : 0 ≤ cθ := by linarith
  have e : cθ ^ (40 * ν) = (cθ ^ (40 : ℝ)) ^ ν := Real.rpow_mul hc0 _ _
  rw [e, ← Real.mul_rpow (Real.rpow_nonneg hc0 _) hδ0.le]
  refine Real.rpow_le_one (mul_nonneg (Real.rpow_nonneg hc0 _) hδ0.le) ?_ hν
  have h40 : cθ ^ (40 : ℝ) = cθ ^ (40 : ℕ) := by exact_mod_cast Real.rpow_natCast cθ 40
  rw [h40]
  have hp : 0 < cθ ^ (40 : ℕ) := by positivity
  calc cθ ^ (40 : ℕ) * δ ≤ cθ ^ (40 : ℕ) * (cθ ^ 40)⁻¹ := mul_le_mul_of_nonneg_left hδ hp.le
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- **The non-regular part under the flower prefix.** -/
theorem nonregPrefix {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix (Stage1ReductionAtMKSel C₀ cP cθ)) (hD7 : SelSumTargetT) :
    WTPrefixP (NonregComponentBoundAtI 17999) := by
  have hm3 := ladderFourierAtMKFace_largeConstantMonotone
  have hm2 := fineSplicedHalfMK_largeConstantMonotone
  have hm1 := coarseSplicedAtMK_largeConstantMonotone
  have hm0 := stage1ReductionAtMKSel_largeConstantMonotone C₀ cP cθ
  have hQ0 := prefix_and hB4 (prefix_and FinalMKCrude.coarseSplicedGateMK
    (prefix_and FinalMKFine.fineSplicedGateHalfMK FinalMKPin.ladderFourierMKFace_prefix hm2 hm3) hm1 (hm2.and hm3))
    hm0 (hm1.and (hm2.and hm3))
  have hQ := prefix_with_stage1_small hQ0 (hm0.and (hm1.and (hm2.and hm3))) (6 * C₀) (by omega)
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨0, fun Pm _ => ?_⟩
  refine ⟨min δ₀ (cθ ^ 40)⁻¹, lt_min hδ₀ (by positivity), fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨Lk, hLk2, hLk⟩ := exists_log_pow_add_one_le (4 * (40 * d) ^ (2 * D + 2))
  refine ⟨C₂, hC₂, max L₀ (max Lk (Real.exp ((Pm : ℝ) + 1))), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLk' : Lk ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLe : Real.exp ((Pm : ℝ) + 1) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨⟨hS1, hcoarse, hfine, hface⟩, hs, -, hd3, habs⟩ := H L hLL₀
  intro hγh
  have hd1 : 1 ≤ d := by omega
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hLe
  have hlogPm : (Pm : ℝ) + 1 ≤ Real.log L := by
    rw [← Real.log_exp ((Pm : ℝ) + 1)]; exact Real.log_le_log (Real.exp_pos _) hLe
  have hlog : 1 ≤ Real.log L := by have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _; linarith
  refine nonreg_at (B := 17999) (Pm := Pm) hcP hcθ hd1 hs habs hlog
    (ctheta_delta_le hcθ hδ.1 (hδ.2.trans (min_le_right _ _)) hν.1.le) ?_ ?_ (budget_17999 hcP' hd1) hS1
    (fun X => hD7 cP cθ hcP hcθ _ hd1 hs hcoarse (hfine hγh) hface X) hγh
  · intro p _
    have h1 := N_quartic_le_log_pow ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ hd1 hlog (p + 1)
    have h2 := hLk L hLk'
    push_cast
    linarith
  · intro p _
    have := le_R_of_log ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ hd1 hlogPm (p + 1)
    omega

end WaveTurbulence.Flower.CompMK
