/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Rest

/-! # B3s MK-SLOTS (integration): mass bookkeeping for `RepresentsIntMK`

* `representsIntMK_C₁_lift`: a constant `c ^ n` carried by the mass moves into the large constant: a representation at
  the record `P` with mass `c ^ n · s` is a representation at `{P with C₁ := c · P.C₁}` with mass `s` (`c ≥ 1`; the
  piece, its kernels and all other parameters are unchanged). This absorbs the frontier presentation constant
  `c_F ^ (16 N)` of the weighted slot and unit bounds.
* `representsIntMK_absorbJ` absorbs the protected loss `L ^ ((31 d + 6) · #cap slots)`;
* `representsIntMK_mono_cPJ` (monotonicity in `cP`), `selMassMK_noneJ` (no selection: mass `b ^ N`).
The last three are copied by source from `AlphaTop.lean` (renamed with suffix `J`, see `COPIED-SHA256SUMS`), so that
the integration does not import `Statement.lean`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.MkSlots

/-- The record with a larger first constant. -/
abbrev withC₁ (P : WTParams) (c : ℝ) : WTParams := {P with C₁ := c * P.C₁}

theorem pow_sub_add_add_ge {c : ℝ} (hc : 1 ≤ c) (n o r : ℕ) : c ^ n ≤ c ^ (n - o) * c ^ (o + r) := by
  rw [← pow_add]
  exact pow_le_pow_right₀ hc (by omega)

/-- **The `C₁`-lift.** -/
theorem representsIntMK_C₁_lift {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP : ℝ}
    {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (c : ℝ) (hc : 1 ≤ c) (h : π.RepresentsIntMK n cP tt base roots (c ^ n * s) val) :
    Stage1PieceMK.RepresentsIntMK (P := withC₁ P c) π n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  set E := P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
    P.L ^ (cP * P.d * (π.nProt : ℝ)) with hE
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) * E with hK
  have hcn : 0 < c ^ n := pow_pos (lt_of_lt_of_le one_pos hc) n
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have h4' : ∫ ξ, ‖w ξ‖ ∂μ ≤ c ^ n * (K * s) := by
    have e : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * (c ^ n * s) = c ^ n * (K * s) := by
      rw [hK, hE]; ring
    rw [← e]; exact h4
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hcn hneg
    linarith
  have hmono : c ^ n * (K * s) ≤ c ^ (n - π.Gsb.order) * c ^ (π.Gsb.order + 2 * R) * (K * s) :=
    mul_le_mul_of_nonneg_right (pow_sub_add_add_ge hc n π.Gsb.order (2 * R)) hKs
  show ∫ ξ, ‖w ξ‖ ∂μ ≤ ((c * P.C₁) * Real.sqrt P.δ) ^ (n - π.Gsb.order) * (c * P.C₁) ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
    P.L ^ (cP * P.d * (π.nProt : ℝ)) * s
  have e2 : ((c * P.C₁) * Real.sqrt P.δ) ^ (n - π.Gsb.order) * (c * P.C₁) ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * s = c ^ (n - π.Gsb.order) * c ^ (π.Gsb.order + 2 * R) * (K * s) := by
    rw [hK, hE, mul_pow, mul_pow, mul_pow]; ring
  rw [e2]
  exact h4'.trans hmono

-- [copied] `MkSlots/AlphaTop.lean` (`representsIntMK_mono_cP`, `selMassMK_none`, `representsIntMK_absorb`), renamed
-- with suffix `J`, see COPIED-SHA256SUMS.
/-- `RepresentsIntMK` is monotone in the protected loss exponent (for `L ≥ 1`). -/
theorem representsIntMK_mono_cPJ {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP cP' : ℝ}
    (hc : cP ≤ cP') (hL : 1 ≤ P.L) {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    {s : ℝ} {val : ℂ} (h : π.RepresentsIntMK n cP tt base roots s val) :
    π.RepresentsIntMK n cP' tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have hexp : P.L ^ (cP * P.d * (π.nProt : ℝ)) ≤ P.L ^ (cP' * P.d * (π.nProt : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by
      have : (0 : ℝ) ≤ P.d * (π.nProt : ℝ) := by positivity
      nlinarith)
  have hpos : 0 < P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have : K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s < 0 := by
      have := mul_neg_of_neg_of_pos hneg hpos
      linarith [this, show K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s = K * s * P.L ^ (cP * P.d * (π.nProt : ℝ))
        from by ring]
    linarith
  calc ∫ ξ, ‖w ξ‖ ∂μ ≤ K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s := h4
    _ = K * s * P.L ^ (cP * P.d * (π.nProt : ℝ)) := by ring
    _ ≤ K * s * P.L ^ (cP' * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP' * P.d * (π.nProt : ℝ)) * s := by ring

/-- With no depth selection, the selected mass is `b^N`. -/
theorem selMassMK_noneJ {R N : ℕ} (b : ℝ) (Rs : Fin (2 * R) → ℝ) (U : Finset (Fin (2 * R))) :
    selMassMK N b Rs (fun _ => none) U = b ^ N := by
  simp [selMassMK]

/-- A loss `L^ℓ` carried by the mass parameter moves into the protected factor when `ℓ ≤ cP·d·nProt`. -/
theorem representsIntMK_absorbJ {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) {n : ℕ} {cP ℓ : ℝ}
    (hL : 1 ≤ P.L) (hℓ : ℓ ≤ cP * P.d * (π.nProt : ℝ)) {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : π.RepresentsIntMK n 0 tt base roots (P.L ^ ℓ * s) val) :
    π.RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ))
  have hexp : P.L ^ ℓ ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL hℓ
  have hpos : 0 < P.L ^ ℓ := Real.rpow_pos_of_pos hL0 _
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have h4' : ∫ ξ, ‖w ξ‖ ∂μ ≤ K * s * P.L ^ ℓ := by
    have : K * P.L ^ ((0 : ℝ) * P.d * (π.nProt : ℝ)) * (P.L ^ ℓ * s) = K * s * P.L ^ ℓ := by
      rw [zero_mul, zero_mul, Real.rpow_zero]; ring
    rw [← this]; exact h4
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc ∫ ξ, ‖w ξ‖ ∂μ ≤ K * s * P.L ^ ℓ := h4'
    _ ≤ K * s * P.L ^ (cP * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * s := by ring
-- [end copied]

end WaveTurbulence.Flower.MkSlots
