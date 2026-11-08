/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMass
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel

/-! # B3s-HELPER7 (general assembly): mass bookkeeping for `RepresentsIntMKSel`

The selected twins of α's `MkSlots.representsIntMK_absorbJ` and `representsIntMK_C₁_lift` (W:MkSlots/IntMass.lean):
only the weight-integral inequality of `FinalMKDefs.RepresentsIntMKSel` changes, the representation is kept.

* `representsIntMKSel_mono_s`: the mass parameter is monotone;
* `representsIntMKSel_absorb`: a loss `L^ℓ` in the mass parameter moves into `L^{cP·d·nProt}` when
  `ℓ ≤ (cP - cP₀)·d·nProt`;
* `representsIntMKSel_C₁_lift`: a factor `c^n` in the mass parameter moves into the large constant `C₁ ↦ c·C₁`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsI

/-- The mass parameter of `RepresentsIntMKSel` is monotone. -/
theorem representsIntMKSel_mono_s {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R)
    (sel : Finset (GBranch π.Gsb.tree)) {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s s' : ℝ} {val : ℂ} (hss : s ≤ s') (hL : 0 ≤ P.L) (hC : 0 ≤ P.C₁)
    (hδ : 0 ≤ P.δ) (h : RepresentsIntMKSel π sel n cP tt base roots s val) :
    RepresentsIntMKSel π sel n cP tt base roots s' val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4.trans ?_, h5⟩
  have hK : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) := by
    have := Real.sqrt_nonneg P.δ
    positivity
  exact mul_le_mul_of_nonneg_left hss hK

/-- **A loss carried by the mass parameter moves into the protected factor.** -/
theorem representsIntMKSel_absorb {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R)
    (sel : Finset (GBranch π.Gsb.tree)) {n : ℕ} {cP₀ cP ℓ : ℝ} (hL : 1 ≤ P.L)
    (hℓ : cP₀ * P.d * (π.nProt : ℝ) + ℓ ≤ cP * P.d * (π.nProt : ℝ)) {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : RepresentsIntMKSel π sel n cP₀ tt base roots (P.L ^ ℓ * s) val) :
    RepresentsIntMKSel π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) with hKdef
  set E := P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) with hE
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ :=
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
  have hEpos : 0 < E := Real.rpow_pos_of_pos hL0 _
  have hexp : P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL hℓ
  have hpos : 0 < P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ :=
    mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hL0 _)
  have h4' : ∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ ≤
      (K * E * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := by
    have e : K * P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * E * (P.L ^ ℓ * s) =
        (K * E * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := by ring
    rw [← e]; exact h4
  have hKs : 0 ≤ K * E * s := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc _ ≤ (K * E * s) * (P.L ^ (cP₀ * P.d * (π.nProt : ℝ)) * P.L ^ ℓ) := h4'
    _ ≤ (K * E * s) * P.L ^ (cP * P.d * (π.nProt : ℝ)) := mul_le_mul_of_nonneg_left hexp hKs
    _ = K * P.L ^ (cP * P.d * (π.nProt : ℝ)) * E * s := by ring

/-- **The large constant absorbs `c^n`** (`C₁ ↦ c·C₁`, `withC₁`). -/
theorem representsIntMKSel_C₁_lift {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R)
    (sel : Finset (GBranch π.Gsb.tree)) {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ} (c : ℝ) (hc : 1 ≤ c)
    (h : RepresentsIntMKSel π sel n cP tt base roots (c ^ n * s) val) :
    RepresentsIntMKSel (P := withC₁ P c) π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hΞ, μ, w, ctr, edge, hinge, freq, h1, h2, h3, ?_, h5⟩
  set E := P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
    P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) with hE
  set K := (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) * E with hK
  have hcn : 0 < c ^ n := pow_pos (lt_of_lt_of_le one_pos hc) n
  have h4' : ∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ ≤ c ^ n * (K * s) := by
    have e : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * (c ^ n * s) =
        c ^ n * (K * s) := by
      rw [hK, hE]; ring
    rw [← e]; exact h4
  have hint0 : 0 ≤ ∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ :=
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
  have hKs : 0 ≤ K * s := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hcn hneg
    linarith
  have hmono : c ^ n * (K * s) ≤ c ^ (n - π.Gsb.order) * c ^ (π.Gsb.order + 2 * R) * (K * s) :=
    mul_le_mul_of_nonneg_right (pow_sub_add_add_ge hc n π.Gsb.order (2 * R)) hKs
  show ∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ ≤
    ((c * P.C₁) * Real.sqrt P.δ) ^ (n - π.Gsb.order) * (c * P.C₁) ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
    P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s
  have e2 : ((c * P.C₁) * Real.sqrt P.δ) ^ (n - π.Gsb.order) * (c * P.C₁) ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s =
      c ^ (n - π.Gsb.order) * c ^ (π.Gsb.order + 2 * R) * (K * s) := by
    rw [hK, hE, mul_pow, mul_pow, mul_pow]; ring
  rw [e2]
  exact h4'.trans hmono

end WaveTurbulence.Flower.MkSlotsI
