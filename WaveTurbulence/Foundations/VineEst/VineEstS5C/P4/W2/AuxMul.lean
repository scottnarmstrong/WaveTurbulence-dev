/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows

/-! # P4-W2 AUX (c): `remRowMul`, the `𝒦` row of a remainder times a bounded spatial multiplier

In the twisted family the remainder function `RT(t₁,t₀,x)` of the exceptional couple/tree sits at the row of momentum `x`; for a twisted state
that is the `𝒦` row, which also carries the `r`-dependent spatial factor `G(r,k)` of the other piece.  `remRowW` has no `r`-dependent factor.
`remRowMul`: the row `f(c₀,c₁,k) · G(r,k)` (with `f` time-continuous, slots arbitrary) with the coefficients `ĉ_m(k) G(r,k)` bounded per mode by
`SNorm_mul_le` (`G r` at weight `0`, the coefficient at the row weight): size `C · 2^{Λ₁} d^{Λ₁} · b · sup_r ‖G r‖_{𝔖^{Λ₁,0}}`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory
  WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams}

/-- One mode times a multiplier. -/
theorem snorm_mulG_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (g G : Mom d → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : SNorm A B g ≠ ⊤) (hG : SNorm A 0 G ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun k => g k * G k) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cg) * SNorm A B g := by
  have hgc : ContDiff ℝ A g := contDiff_of_SNorm_le' hA g (SNorm A B g).toReal (by rw [ENNReal.ofReal_toReal hg])
  have hGc : ContDiff ℝ A G := contDiff_of_SNorm_le' hA G Cg hG
  have h := SNorm_mul_le hd G g hGc hgc hCg ENNReal.toReal_nonneg hG (by rw [ENNReal.ofReal_toReal hg])
  have e : (fun k => g k * G k) = fun k => G k * g k := funext fun k => mul_comm _ _
  rw [e]
  refine h.trans (le_of_eq ?_)
  have hK : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * Cg := by positivity
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hg]

/-- **The row `f(c₀,c₁,k) G(r,k)`.** -/
theorem remRowMul (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) (hd : 1 ≤ P.d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx), D.wN = Λ₁ →
      rowOrder D (Sum.inl w₀) = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (G : Mom P.d → Mom P.d → ℂ) (b : ℝ≥0∞) (Cg : ℝ),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f t k) →
      XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ f < b →
      (⨆ r : Mom P.d, SNorm Λ₁ 0 (G r)) ≤ ENNReal.ofReal Cg →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀), (∀ cl r k, ![cl 0, cl 1] ∈ B → R.W cl r k = f ![cl 0, cl 1] k * G r k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧ R.b ≤ C * b * ENNReal.ofReal Cg ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_ae (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁), ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,
    fun D hI w₀ h1 h2 s q B f G b Cg hb hc hi hcont hX hGb => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B f f b hc hi hcont (Filter.Eventually.of_forall fun _ _ _ => rfl) hX
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  have hGr : ∀ r, SNorm Λ₁ 0 (G r) ≤ ENNReal.ofReal (max Cg 0) := fun r =>
    (le_iSup (fun r => SNorm Λ₁ 0 (G r)) r).trans (hGb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hcbtop : C * b ≠ ⊤ := ENNReal.mul_ne_top hC hb
  have hcm : ∀ m, SNorm Λ₁ Λ₂ (c m) ≠ ⊤ := fun m => by
    refine ne_top_of_le_ne_top hcbtop ?_
    refine le_trans ?_ hcb
    refine le_trans ?_ (ENNReal.le_tsum m)
    exact le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ0 _)
  have hK : ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) =
      ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * ENNReal.ofReal Cg := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rcases le_total Cg 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D (Sum.inl w₀)) (fun m r k => c m k * G r k) ≤
      C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * b * ENNReal.ofReal Cg := by
    unfold coefBound
    rw [h1, h2]
    calc ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * ⨆ r : Mom P.d, SNorm Λ₁ Λ₂ (fun k => c m k * G r k)
        ≤ ∑' m : Fin 3 → ℤ, ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) *
            (maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ Λ₂ (c m)) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          rw [mul_left_comm]
          refine mul_le_mul' le_rfl (iSup_le fun r => ?_)
          exact snorm_mulG_le hd hΛ (c m) (G r) hCg0 (hcm m) (hGr r)
      _ = ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) *
            ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ Λ₂ (c m) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) * (C * b) := mul_le_mul' le_rfl hcb
      _ = C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * b * ENNReal.ofReal Cg := by
          rw [hK]; ring
  have hbfin : C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * b * ENNReal.ofReal Cg ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hb) ENNReal.ofReal_ne_top
  refine ⟨RowData.ofModes (θ := 6 * P.η ^ 6) (Sum.inl w₀) ![s 0, s 1, s 0] (fun m r k => c m k * G r k)
    (C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) * b * ENNReal.ofReal Cg) hbfin hfs (fun w hw => absurd hw (by simp)),
    fun cl r k hcl => RowData.ofModes_W (by
      have h := (hcs cl hcl k).mul_right (G r k)
      convert h using 2 with m
      ring), fun _ => rfl, le_rfl, RowData.ofModes_ae hθ0 hI (Sum.inl w₀) _ _ _ _ _ _⟩

end WaveTurbulence.VineEstS5C.P4.W2
