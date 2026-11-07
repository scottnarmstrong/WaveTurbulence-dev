/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemMulD
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemModes

/-! # P4-W2 (R78): remainder rows with a continuity set `Bc` (F-AUX-CONT for remainders)

`remRowMulDC`: `remRowMulD` with `f` only `ContinuousOn Bc` and the clock slots in `Bc`.  `remRowC`: the plain remainder row of any `ρ` (`remRowWS` with a continuity set).
`oneRowC`: the constant row `1` (the trivial `ℒ` row of a piece whose time factors all sit on the `𝒦` row). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory
  WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams}

/-- **The row `f(c₀,c₁,k) G(r,k)`.** -/
theorem remRowMulDC (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) (hd : 1 ≤ P.d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx), D.wN = Λ₁ →
      rowOrder D (Sum.inl w₀) = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B Bc : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (G : Mom P.d → Mom P.d → ℂ) (b : ℝ≥0∞) (Cg : ℝ),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → Bc ⊆ B → Bc ⊆ closure (interior Bc) →
      (∀ k, ContinuousOn (fun t => f t k) Bc) →
      XNormRestr (6 * P.η ^ 6) Λ₁ 0 B Set.univ f < b →
      (⨆ r : Mom P.d, SNorm Λ₁ Λ₂ (G r)) ≤ ENNReal.ofReal Cg →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀), (∀ cl r k, ![cl 0, cl 1] ∈ Bc → R.W cl r k = f ![cl 0, cl 1] k * G r k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧ R.b ≤ C * b * ENNReal.ofReal Cg ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_C (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := 0) hΛ
  refine ⟨C * ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁), ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,
    fun D hI w₀ h1 h2 s q B Bc f G b Cg hb hc hi hBcB hBci hcont hX hGb => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B Bc f b hc hi hBcB hBci hcont hX
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


/-- **The plain remainder row** `f(c₀,c₁,k)` (any row `ρ`; independent of `r`), with a continuity set. -/
theorem remRowC (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (ρ : Row D), D.wN = Λ₁ → rowOrder D ρ = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B Bc : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (b : ℝ≥0∞),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → Bc ⊆ B → Bc ⊆ closure (interior Bc) →
      (∀ k, ContinuousOn (fun t => f t k) Bc) → XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ B Set.univ f < b →
      ∃ R : RowData D (6 * P.η ^ 6) ρ, (∀ cl r k, ![cl 0, cl 1] ∈ Bc → R.W cl r k = f ![cl 0, cl 1] k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧ R.b = C * b ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_C (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C, hC, fun D hI ρ h1 h2 s q B Bc f b hb hc hi hBcB hBci hcont hX => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B Bc f b hc hi hBcB hBci hcont hX
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D ρ) (fun m _ k => c m k) ≤ C * b := by
    unfold coefBound
    rw [h1, h2]
    refine le_trans (le_of_eq (tsum_congr fun m => ?_)) hcb
    congr 1
    exact iSup_const
  refine ⟨RowData.ofModes (θ := 6 * P.η ^ 6) ρ ![s 0, s 1, s 0] (fun m _ k => c m k) (C * b) (ENNReal.mul_ne_top hC hb) hfs
    (fun _ _ _ _ _ _ => rfl), fun cl r k hcl => RowData.ofModes_W (hcs cl hcl k), fun _ => rfl, rfl,
    RowData.ofModes_ae hθ0 hI ρ _ _ _ _ _ _⟩

/-- **The constant row `1`** (any row `ρ`): the trivial `ℒ` row. -/
theorem oneRowC (hη0 : 0 < P.η) (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (vb : D.S.VIdx) (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) :
    ∃ R : RowData D (6 * P.η ^ 6) (Sum.inr vb), (∀ c r k, R.W c r k = 1) ∧ (∀ i, R.slot i = s i) ∧ R.b ≤ ENNReal.ofReal 1 ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  classical
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D (Sum.inr vb)) (fun (m : Fin 3 → ℤ) (_ : Mom P.d) (_ : Mom P.d) => if m = 0 then (1 : ℂ) else 0) ≤ ENNReal.ofReal 1 := by
    unfold coefBound
    rw [tsum_eq_single (0 : Fin 3 → ℤ)]
    · have h1 : (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr vb)) (fun _ : Mom P.d => (if (0 : Fin 3 → ℤ) = 0 then (1 : ℂ) else 0))) ≤ ENNReal.ofReal 1 :=
        iSup_le fun _ => by rw [show rowOrder D (Sum.inr vb) = 0 from rfl]; simpa using SNorm_one_le (d := P.d) D.wN
      have h2 : maxBracketPow (6 * P.η ^ 6) (half (0 : Fin 3 → ℤ)) = 1 := by
        unfold maxBracketPow
        simp [half]
      rw [h2, one_mul]; exact h1
    · intro m hm
      have : (fun _ : Mom P.d => (if m = 0 then (1 : ℂ) else 0)) = fun _ => 0 := by simp [hm]
      simp only [hm, ite_false, this, SNorm_zero_fun, iSup_const, mul_zero]
  refine ⟨{ W := fun _ _ _ => 1
            slot := s
            c := fun m _ _ => if m = 0 then 1 else 0
            b := ENNReal.ofReal 1
            b_ne_top := ENNReal.ofReal_ne_top
            fs := hfs
            indepW := fun _ _ _ _ _ _ => rfl
            indepC := fun _ _ _ _ _ _ => rfl },
    fun _ _ _ => rfl, fun _ => rfl, le_rfl, ?_⟩
  intro tt htt
  filter_upwards with τ r k
  have : (fun m : Fin 3 → ℤ => (if m = 0 then (1 : ℂ) else 0) * fsPhase m (fun i => slotVal D τ tt (s i))) =
      fun m => if m = 0 then 1 else 0 := by
    funext m
    by_cases hm : m = 0
    · subst hm
      have h0 : (fun i : Fin 3 => (((0 : Fin 3 → ℤ) i : ℤ) : ℝ) / 2) = 0 := by funext i; simp
      unfold fsPhase
      rw [h0, LinearMap.map_zero]
      simp
    · simp [hm]
  show HasSum (fun m : Fin 3 → ℤ => (if m = 0 then (1 : ℂ) else 0) * fsPhase m (fun i => slotVal D τ tt (s i))) 1
  rw [this]
  simpa using hasSum_ite_eq (0 : Fin 3 → ℤ) (1 : ℂ)

end WaveTurbulence.VineEstS5C.P4.W2
