/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Orders
public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeId

/-!
# RA2 REGREF, couples: B2.1 items (1), (3) couple part, (4) from RA1 (TARGET Props `regref1`–`regref3`)

TARGET's proof of `regref1`–`regref3` (L1171–L1173): DH23 Prop 6.1 applies (RA1, here the named obligation
`RA1Couple`, stated in layer `0`), because

* `K*_𝒬` and `(K*_𝒬)_app` are invariant under translating all times by `r` (`KQstar_shift`, `app_shift`, which use
  the telescoping `∑ ζ_𝔫 Ω_𝔫 = 0` of couples, `sum_sign_omega_couple`), and the `𝔛` restriction norms are
  translation invariant (`XNormRestr_shift_le`, `XNorm00Restr_shift_le`);
* the inputs `F_r = φ(δr) + R_r` are real and bounded in `𝔖^{40d,40d}` uniformly (`exists_SNormR_bound_of_continuousOn`,
  `SNormR_input_le`, with `L^{-θ_r} ≤ 1`);
* every order `n ≤ N_{p+1}^4` is polylogarithmic (`le_logPow_ordExp`).

Item (4) is MEXP's `regularAsymptotics_item4` (J6 WKE-ID).

**`regularAsymptotics_couples`** is B2.1 with the conjuncts (1), (3) (couples) and (4), verbatim.
Constants: `C₁ := C` of RA1 for the input bound `B₁ + 1` (`B₁` the `𝔖^{40d,40d}` bound of `φ` on `[0, τ★]`),
`ν₀ := 1`, `δ₀ := δ₁` of RA1, `C₂ := 1`, `L₀ := max (max 2 L₁) e` with `L₁` RA1's `L₀` for the order exponent
`A(d, 𝔇)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Regref

open TTree

theorem sub_mem_timeBox {q q' : ℝ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox q q') :
    ts - (fun _ => q) ∈ timeBox 0 (q' - q) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Pi.sub_apply] <;> linarith

theorem sub_mem_timeBox_self {q : ℝ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox q q) :
    ts - (fun _ => q) ∈ timeBox 0 0 := by
  simpa using sub_mem_timeBox h

theorem regBound_one (P : WTParams) (n : ℕ) :
    regBound P n 1 = ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(gam1 P.d P.γ - Real.sqrt P.η))) := by
  simp only [regBound, Nat.cast_one, mul_one, gamma1_eq]

theorem one_le_log_of_exp_le {L : ℝ} (h : Real.exp 1 ≤ L) : 1 ≤ Real.log L := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) h

/-- The input bound of RA1 at `F_r = φ(δr) + R_r`. -/
theorem SNormR_F_le (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {B₁ : ℝ} (hB₁ : 0 ≤ B₁)
    (hφ : ∀ τ ∈ Icc 0 P.τstar, SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal B₁)
    {r : ℕ} (hr : P.δ * r ∈ Icc 0 P.τstar) {R : Mom P.d → ℝ} (hR : InputRemainder P R r) :
    SNormR (40 * P.d) (40 * P.d) (fun k => P.φ (P.δ * r) k + R k) ≤ ENNReal.ofReal (B₁ + 1) := by
  refine SNormR_input_le (by omega) (P.φ (P.δ * r)) hB₁ zero_le_one (hφ _ hr) (hR.trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos hL ?_)
  have : 0 ≤ P.theta r := by unfold WTParams.theta; positivity
  linarith

end WaveTurbulence.Regref
