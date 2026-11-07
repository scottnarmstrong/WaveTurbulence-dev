/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxMul
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemModes

/-! # P4-W2 (R78, F-REM-ORIENT): `remRowShiftMul`, the `𝒦` row of a SHIFTED remainder times a weight-`0` multiplier

The row `cutW (f(c₀,c₁,k + u r) G(r,k))`, `|u| ≤ 1`: the remainder `f` (a couple remainder at the lower joint `low = ret + ε r`) carries the row weight, `G` has weight `0`.
The coefficients are `ĉ_m(k + u r) G(r,k)` (cut off to `‖r‖ ≤ 1`), bounded by `SNorm_translate_le` then `SNorm_mul_le`.  Copy-edit of `AuxMul.remRowMul`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory
  WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams}

/-- A shifted mode (weight `B`) times a weight-`0` multiplier. -/
theorem snorm_shiftmulG_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (g G : Mom d → ℂ) (a : Mom d) (ha : ‖a‖ ≤ 1) {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hg : SNorm A B g ≠ ⊤) (hG : SNorm A 0 G ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun k => g (k + a) * G k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cg) * (ENNReal.ofReal ((2 : ℝ) ^ B * (d : ℝ) ^ A) * SNorm A B g) := by
  have hgc : ContDiff ℝ A g := contDiff_of_SNorm_le' hA g (SNorm A B g).toReal (by rw [ENNReal.ofReal_toReal hg])
  have hg0 : 0 ≤ (SNorm A B g).toReal := ENNReal.toReal_nonneg
  have ht := SNorm_translate_le hd hgc hg0 (by rw [ENNReal.ofReal_toReal hg]) a ha
  have hsc : ContDiff ℝ A (fun k => g (k + a)) := hgc.comp (contDiff_id.add contDiff_const)
  have h := snorm_mulG_le hd hA (fun k => g (k + a)) G hCg
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ht) hG
  refine h.trans (mul_le_mul' le_rfl (ht.trans (le_of_eq ?_)))
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hg]

/-- **The row `cutW (f(c₀,c₁,k + u r) G(r,k))`.** -/
theorem remRowShiftMul (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) (hd : 1 ≤ P.d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx), D.wN = Λ₁ →
      rowOrder D (Sum.inl w₀) = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B Bc : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (G : Mom P.d → Mom P.d → ℂ) (u : ℝ) (b : ℝ≥0∞) (Cg : ℝ),
      |u| ≤ 1 → b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → Bc ⊆ B → Bc ⊆ closure (interior Bc) →
      (∀ k, ContinuousOn (fun t => f t k) Bc) →
      XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ f < b →
      (∀ r : Mom P.d, ‖r‖ ≤ 1 → SNorm Λ₁ 0 (G r) ≤ ENNReal.ofReal Cg) →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀), (∀ cl r k, ‖r‖ ≤ 1 → ![cl 0, cl 1] ∈ Bc → R.W cl r k = f ![cl 0, cl 1] (k + u • r) * G r k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧
        R.b ≤ C * b * ENNReal.ofReal Cg ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_C (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * ENNReal.ofReal ((2 : ℝ) ^ Λ₂ * (P.d : ℝ) ^ Λ₁),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top,
    fun D hI w₀ h1 h2 s q B Bc f G u b Cg hu hb hc hi hBcB hBci hcont hX hGb => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B Bc f b hc hi hBcB hBci hcont hX
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  have hGr : ∀ r, ‖r‖ ≤ 1 → SNorm Λ₁ 0 (G r) ≤ ENNReal.ofReal (max Cg 0) := fun r hr =>
    (hGb r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hcbtop : C * b ≠ ⊤ := ENNReal.mul_ne_top hC hb
  have hcm : ∀ m, SNorm Λ₁ Λ₂ (c m) ≠ ⊤ := fun m => by
    refine ne_top_of_le_ne_top hcbtop ?_
    refine le_trans ?_ hcb
    refine le_trans ?_ (ENNReal.le_tsum m)
    exact le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ0 _)
  have hnu : ∀ r : Mom P.d, ‖r‖ ≤ 1 → ‖u • r‖ ≤ 1 := fun r hr => by
    rw [norm_smul, Real.norm_eq_abs]; nlinarith [abs_nonneg u, norm_nonneg r]
  have hK : ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) =
      ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * ENNReal.ofReal Cg := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rcases le_total Cg 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  set K1 : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) with hK1
  set K2 : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ Λ₂ * (P.d : ℝ) ^ Λ₁) with hK2
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D (Sum.inl w₀))
      (fun m r k => cutW (fun r k => c m (k + u • r) * G r k) r k) ≤ C * K1 * K2 * b * ENNReal.ofReal Cg := by
    unfold coefBound
    rw [h1, h2]
    calc ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) *
          ⨆ r : Mom P.d, SNorm Λ₁ Λ₂ (cutW (fun r k => c m (k + u • r) * G r k) r)
        ≤ ∑' m : Fin 3 → ℤ, (K1 * ENNReal.ofReal Cg * K2) *
            (maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ Λ₂ (c m)) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          rw [mul_left_comm]
          refine mul_le_mul' le_rfl (snorm_cutW_le _ fun r hr => ?_)
          have := snorm_shiftmulG_le hd hΛ (c m) (G r) (u • r) (hnu r hr) hCg0 (hcm m) (hGr r hr)
          rw [hK] at this
          exact this.trans (le_of_eq (by simp only [hK2]; ring))
      _ = (K1 * ENNReal.ofReal Cg * K2) *
            ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ Λ₂ (c m) := ENNReal.tsum_mul_left
      _ ≤ (K1 * ENNReal.ofReal Cg * K2) * (C * b) := mul_le_mul' le_rfl hcb
      _ = C * K1 * K2 * b * ENNReal.ofReal Cg := by ring
  have hbfin : C * K1 * K2 * b * ENNReal.ofReal Cg ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) hb) ENNReal.ofReal_ne_top
  refine ⟨RowData.ofModes (θ := 6 * P.η ^ 6) (Sum.inl w₀) ![s 0, s 1, s 0]
    (fun m r k => cutW (fun r k => c m (k + u • r) * G r k) r k)
    (C * K1 * K2 * b * ENNReal.ofReal Cg) hbfin hfs (fun w hw => absurd hw (by simp)),
    fun cl r k hr hcl => RowData.ofModes_W (by
      have h := (hcs cl hcl (k + u • r)).mul_right (G r k)
      show HasSum (fun m : Fin 3 → ℤ => cutW (fun r k => c m (k + u • r) * G r k) r k * fsPhase m cl)
        (f ![cl 0, cl 1] (k + u • r) * G r k)
      simp only [cutW_of_le hr]
      convert h using 2 with m
      ring), fun _ => rfl, le_rfl, RowData.ofModes_ae hθ0 hI (Sum.inl w₀) _ _ _ _ _ _⟩

end WaveTurbulence.VineEstS5C.P4.W2
