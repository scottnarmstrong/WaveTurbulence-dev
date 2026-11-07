/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows

/-! # P4-W2 (b1): `remRowMulD`, the `𝒦` row of a weight-0 remainder (a tree remainder) times a DECAYING multiplier

Copy-edit of `AuxMul.remRowMul` (that file is unchanged): the remainder `f` has weight `0`, the multiplier `G` carries the row weight (`rowOrder`, the decaying couple factor),
so that the product has the row weight (`SNorm_mul_le` with the weight-`0` factor first).  `AuxMul`'s version has `f` at the row weight and `G` at weight `0`. -/

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

/-- One mode (weight `0`) times a decaying multiplier (weight `B`). -/
theorem snorm_mulGD_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (g G : Mom d → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : SNorm A 0 g ≠ ⊤) (hG : SNorm A B G ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun k => g k * G k) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cg) * SNorm A 0 g := by
  have hgc : ContDiff ℝ A g := contDiff_of_SNorm_le' hA g (SNorm A 0 g).toReal (by rw [ENNReal.ofReal_toReal hg])
  have hGc : ContDiff ℝ A G := contDiff_of_SNorm_le' hA G Cg hG
  have h := SNorm_mul_le hd g G hgc hGc ENNReal.toReal_nonneg hCg (by rw [ENNReal.ofReal_toReal hg]) hG
  refine h.trans (le_of_eq ?_)
  have hK : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * Cg := by positivity
  rw [show (2 : ℝ) ^ A * (d : ℝ) ^ A * (SNorm A 0 g).toReal * Cg = (2 ^ A * (d : ℝ) ^ A * Cg) * (SNorm A 0 g).toReal by ring,
    ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hg]

/-- **The row `f(c₀,c₁,k) G(r,k)`.** -/
theorem remRowMulD (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) (hd : 1 ≤ P.d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx), D.wN = Λ₁ →
      rowOrder D (Sum.inl w₀) = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (G : Mom P.d → Mom P.d → ℂ) (b : ℝ≥0∞) (Cg : ℝ),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f t k) →
      XNormRestr (6 * P.η ^ 6) Λ₁ 0 B Set.univ f < b →
      (⨆ r : Mom P.d, SNorm Λ₁ Λ₂ (G r)) ≤ ENNReal.ofReal Cg →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀), (∀ cl r k, ![cl 0, cl 1] ∈ B → R.W cl r k = f ![cl 0, cl 1] k * G r k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧ R.b ≤ C * b * ENNReal.ofReal Cg ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_ae (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := 0) hΛ
  refine ⟨C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁), ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,
    fun D hI w₀ h1 h2 s q B f G b Cg hb hc hi hcont hX hGb => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B f f b hc hi hcont (Filter.Eventually.of_forall fun _ _ _ => rfl) hX
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  have hGr : ∀ r, SNorm Λ₁ Λ₂ (G r) ≤ ENNReal.ofReal (max Cg 0) := fun r =>
    (le_iSup (fun r => SNorm Λ₁ Λ₂ (G r)) r).trans (hGb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hcbtop : C * b ≠ ⊤ := ENNReal.mul_ne_top hC hb
  have hcm : ∀ m, SNorm Λ₁ 0 (c m) ≠ ⊤ := fun m => by
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
            (maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ 0 (c m)) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          rw [mul_left_comm]
          refine mul_le_mul' le_rfl (iSup_le fun r => ?_)
          exact snorm_mulGD_le hd hΛ (c m) (G r) hCg0 (hcm m) (hGr r)
      _ = ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁ * max Cg 0) *
            ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ 0 (c m) := ENNReal.tsum_mul_left
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
