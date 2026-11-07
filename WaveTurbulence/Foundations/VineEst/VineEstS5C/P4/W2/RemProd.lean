/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemProd1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.FSAe
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemModes

/-! # P4-W2 (R78, F-REM-ORIENT): `remRowProd`, the three-clock row of a shifted remainder times a remainder

The `𝒦` row `cutW (f(c₀,c₂,k + u r) g(c₁,c₂,k))` of two remainders sharing the clock `c₂`: the couple remainder `f` (row weight `Λ₂`, shifted to the lower joint) and the tree remainder `g` (weight `0`).
Its modes are the convolution in the shared clock: `c_m(r,k) = ∑'_p â_{(m₀,p)}(k + u r) b̂_{(m₁, m₂-p)}(k)` (cut off to `‖r‖ ≤ 1`); the weights are submultiplicative
(`maxBracketPow_merge_le`), the series is bounded by `snorm_tsum_le`, and the expansion is the Cauchy product regrouped along the bijection `(m,p) ↔ (a,b)`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory
  WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams}

/-- The sup norm of a function with finite `𝔖` norm. -/
theorem norm_le_of_snorm {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℂ) {C : ℝ} (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C)
    (x : Mom d) : ‖f x‖ ≤ C := by
  have hc : ContDiff ℝ A f := contDiff_of_SNorm_le' hA f C h
  have := SNorm_frechet_pointwise f hc C hC h (Nat.zero_le A) x
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at this
  exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_jbr x))) this

theorem mergeMode_eq (m : Fin 3 → ℤ) (p : ℤ) : mergeMode ![m 0, p] ![m 1, m 2 - p] = m := by
  funext i; fin_cases i <;> simp [mergeMode]

/-- The regrouping bijection `(m, p) ↔ (a, b)`. -/
def mergeEquiv : (Fin 3 → ℤ) × ℤ ≃ (Fin 2 → ℤ) × (Fin 2 → ℤ) where
  toFun q := (![q.1 0, q.2], ![q.1 1, q.1 2 - q.2])
  invFun ab := (mergeMode ab.1 ab.2, ab.1 1)
  left_inv q := by
    obtain ⟨m, p⟩ := q
    refine Prod.ext ?_ (by simp)
    exact mergeMode_eq m p
  right_inv ab := by
    obtain ⟨a, b⟩ := ab
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp [mergeMode]
    · funext i; fin_cases i <;> simp [mergeMode]

/-- **The expansion of a product of two remainders** (Cauchy product regrouped along `mergeEquiv`). -/
theorem hasSum_merge (a b : (Fin 2 → ℤ) → Mom P.d → ℂ) (k' k : Mom P.d) (t0 t1 t2 : ℝ) (F G : ℂ)
    (hFa : HasSum (fun m => a m k' * fsPhase m ![t0, t2]) F) (hGb : HasSum (fun m => b m k * fsPhase m ![t1, t2]) G)
    (hna : Summable fun m => ‖a m k'‖) (hnb : Summable fun m => ‖b m k‖) :
    HasSum (fun m : Fin 3 → ℤ => (∑' p : ℤ, a ![m 0, p] k' * b ![m 1, m 2 - p] k) * fsPhase m ![t0, t1, t2]) (F * G) := by
  have hph : ∀ m : Fin 2 → ℤ, ‖fsPhase m ![t0, t2]‖ = 1 := fun m => by simp [fsPhase]
  have hph' : ∀ m : Fin 2 → ℤ, ‖fsPhase m ![t1, t2]‖ = 1 := fun m => by simp [fsPhase]
  have hXn : Summable fun m => ‖a m k' * fsPhase m ![t0, t2]‖ := by simpa [norm_mul, hph] using hna
  have hYn : Summable fun m => ‖b m k * fsPhase m ![t1, t2]‖ := by simpa [norm_mul, hph'] using hnb
  have hP := hFa.mul hGb (summable_mul_of_summable_norm hXn hYn)
  have hP' := (mergeEquiv.hasSum_iff).2 hP
  have hfib : ∀ m : Fin 3 → ℤ, HasSum (fun p : ℤ => ((a ![m 0, p] k' * fsPhase ![m 0, p] ![t0, t2]) *
      (b ![m 1, m 2 - p] k * fsPhase ![m 1, m 2 - p] ![t1, t2]))) ((∑' p : ℤ, a ![m 0, p] k' * b ![m 1, m 2 - p] k) *
        fsPhase m ![t0, t1, t2]) := by
    intro m
    have hs : Summable fun p : ℤ => ((a ![m 0, p] k' * fsPhase ![m 0, p] ![t0, t2]) *
        (b ![m 1, m 2 - p] k * fsPhase ![m 1, m 2 - p] ![t1, t2])) := by
      have := hP'.summable.prod_factor m
      simpa [mergeEquiv, Function.comp] using this
    have heq : (fun p : ℤ => ((a ![m 0, p] k' * fsPhase ![m 0, p] ![t0, t2]) *
        (b ![m 1, m 2 - p] k * fsPhase ![m 1, m 2 - p] ![t1, t2]))) =
        fun p => (a ![m 0, p] k' * b ![m 1, m 2 - p] k) * fsPhase m ![t0, t1, t2] := by
      funext p
      have := fsPhase_merge ![m 0, p] ![m 1, m 2 - p] t0 t1 t2
      rw [mergeMode_eq] at this
      rw [this]; ring
    rw [heq]
    rw [heq] at hs
    rw [← tsum_mul_right]; exact hs.hasSum
  exact hP'.prod_fiberwise hfib

/-- **The three-clock row `cutW (f(c₀,c₂,k + u r) g(c₁,c₂,k))`** of a shifted remainder `f` (row weight `Λ₂`) times a remainder `g` (weight `0`) with a shared clock. -/
theorem remRowProd (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) (hη0 : 0 < P.η) (hd : 1 ≤ P.d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx), D.wN = Λ₁ →
      rowOrder D (Sum.inl w₀) = Λ₂ →
      ∀ (s : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (qf qg : Fin 2 → ℝ) (Bf Bg Bcf Bcg : Set (Fin 2 → ℝ))
      (f g : (Fin 2 → ℝ) → Mom P.d → ℂ) (u : ℝ) (bf bg : ℝ≥0∞),
      |u| ≤ 1 → bf ≠ ⊤ → bg ≠ ⊤ → Bf ⊆ cell qf → Bf ⊆ closure (interior Bf) → Bg ⊆ cell qg → Bg ⊆ closure (interior Bg) →
      Bcf ⊆ Bf → Bcf ⊆ closure (interior Bcf) → Bcg ⊆ Bg → Bcg ⊆ closure (interior Bcg) →
      (∀ k, ContinuousOn (fun t => f t k) Bcf) → (∀ k, ContinuousOn (fun t => g t k) Bcg) →
      XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ Bf Set.univ f < bf → XNormRestr (6 * P.η ^ 6) Λ₁ 0 Bg Set.univ g < bg →
      ∃ R : RowData D (6 * P.η ^ 6) (Sum.inl w₀),
        (∀ cl r k, ‖r‖ ≤ 1 → ![cl 0, cl 2] ∈ Bcf → ![cl 1, cl 2] ∈ Bcg → R.W cl r k = f ![cl 0, cl 2] (k + u • r) * g ![cl 1, cl 2] k) ∧
        (∀ i, R.slot i = s i) ∧ R.b ≤ C * bf * bg ∧ R.Ae hI := by
  have hθ0 : 0 ≤ 6 * P.η ^ 6 := by positivity
  obtain ⟨Cf, hCf, hFf⟩ := fs_expansion_C (r := 2) (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  obtain ⟨Cg, hCg, hFg⟩ := fs_expansion_C (r := 2) (d := P.d) hθ0 (Λ₁ := Λ₁) (Λ₂ := 0) hΛ
  set K1 : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ Λ₁ * (P.d : ℝ) ^ Λ₁) with hK1
  set K2 : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ Λ₂ * (P.d : ℝ) ^ Λ₁) with hK2
  set K3 : ℝ≥0∞ := ENNReal.ofReal ((P.d : ℝ) ^ Λ₁) with hK3
  set κ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 2 ^ (6 * P.η ^ 6)) with hκ
  have hKfin : κ * K1 * K2 * K3 ≠ ⊤ := by
    simp only [hκ, hK1, hK2, hK3]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  refine ⟨κ * K1 * K2 * K3 * Cf * Cg, ENNReal.mul_ne_top (ENNReal.mul_ne_top hKfin hCf) hCg,
    fun D hI w₀ h1 h2 s qf qg Bf Bg Bcf Bcg f g u bf bg hu hbf hbg hcf hif hcg hig hBf hBfi hBg hBgi hcontf hcontg hXf hXg => ?_⟩
  obtain ⟨a, has, hab⟩ := hFf qf Bf Bcf f bf hcf hif hBf hBfi hcontf hXf
  obtain ⟨b, hbs, hbb⟩ := hFg qg Bg Bcg g bg hcg hig hBg hBgi hcontg hXg
  have hW1 : ∀ m : Fin 2 → ℤ, 1 ≤ maxBracketPow (6 * P.η ^ 6) (half m) := fun m => one_le_maxBracketPow hθ0 _
  have habtop : Cf * bf ≠ ⊤ := ENNReal.mul_ne_top hCf hbf
  have hbbtop : Cg * bg ≠ ⊤ := ENNReal.mul_ne_top hCg hbg
  have hSa : ∀ m, SNorm Λ₁ Λ₂ (a m) ≠ ⊤ := fun m => by
    refine ne_top_of_le_ne_top habtop (le_trans ?_ hab)
    exact le_trans (le_mul_of_one_le_left bot_le (hW1 m))
      (ENNReal.le_tsum (f := fun m => maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ Λ₂ (a m)) m)
  have hSb : ∀ m, SNorm Λ₁ 0 (b m) ≠ ⊤ := fun m => by
    refine ne_top_of_le_ne_top hbbtop (le_trans ?_ hbb)
    exact le_trans (le_mul_of_one_le_left bot_le (hW1 m))
      (ENNReal.le_tsum (f := fun m => maxBracketPow (6 * P.η ^ 6) (half m) * SNorm Λ₁ 0 (b m)) m)
  -- summability of the sup norms
  have hsumA : Summable fun m => (SNorm Λ₁ Λ₂ (a m)).toReal := by
    refine ENNReal.summable_toReal (ne_top_of_le_ne_top habtop (le_trans (ENNReal.tsum_le_tsum fun m => ?_) hab))
    exact le_mul_of_one_le_left bot_le (hW1 m)
  have hsumB : Summable fun m => (SNorm Λ₁ 0 (b m)).toReal := by
    refine ENNReal.summable_toReal (ne_top_of_le_ne_top hbbtop (le_trans (ENNReal.tsum_le_tsum fun m => ?_) hbb))
    exact le_mul_of_one_le_left bot_le (hW1 m)
  have hnorma : ∀ k, Summable fun m => ‖a m k‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => norm_le_of_snorm hΛ (a m) ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal (hSa m)]) k) hsumA
  have hnormb : ∀ k, Summable fun m => ‖b m k‖ := fun k =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => norm_le_of_snorm hΛ (b m) ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal (hSb m)]) k) hsumB
  -- the term bounds
  set Wf : (Fin 2 → ℤ) → ℝ≥0∞ := fun m => maxBracketPow (6 * P.η ^ 6) (half m) with hWf
  set Wm : (Fin 3 → ℤ) → ℝ≥0∞ := fun m => maxBracketPow (6 * P.η ^ 6) (half m) with hWm
  set E : (Fin 3 → ℤ) → ℤ → ℝ≥0∞ := fun m p => K1 * K2 * (SNorm Λ₁ Λ₂ (a ![m 0, p]) * SNorm Λ₁ 0 (b ![m 1, m 2 - p])) with hE
  set FF : (Fin 2 → ℤ) × (Fin 2 → ℤ) → ℝ≥0∞ := fun ab => (κ * K1 * K2) * ((Wf ab.1 * SNorm Λ₁ Λ₂ (a ab.1)) *
    (Wf ab.2 * SNorm Λ₁ 0 (b ab.2))) with hFF
  have hKfin' : κ * K1 * K2 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp only [hκ]; exact ENNReal.ofReal_ne_top) (by simp only [hK1]; exact ENNReal.ofReal_ne_top)) (by simp only [hK2]; exact ENNReal.ofReal_ne_top)
  have hTot : ∑' m : Fin 3 → ℤ, Wm m * ∑' p : ℤ, E m p ≤ κ * K1 * K2 * ((Cf * bf) * (Cg * bg)) := by
    calc ∑' m, Wm m * ∑' p, E m p = ∑' m : Fin 3 → ℤ, ∑' p : ℤ, Wm m * E m p := by
          refine tsum_congr fun m => ?_; exact ENNReal.tsum_mul_left.symm
      _ ≤ ∑' m : Fin 3 → ℤ, ∑' p : ℤ, (κ * K1 * K2) * ((Wf ![m 0, p] * SNorm Λ₁ Λ₂ (a ![m 0, p])) *
            (Wf ![m 1, m 2 - p] * SNorm Λ₁ 0 (b ![m 1, m 2 - p]))) := by
          refine ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun p => ?_
          have hw := maxBracketPow_merge_le hθ0 ![m 0, p] ![m 1, m 2 - p]
          rw [mergeMode_eq] at hw
          calc Wm m * E m p ≤ (κ * (Wf ![m 0, p] * Wf ![m 1, m 2 - p])) * E m p := mul_le_mul' hw le_rfl
            _ = (κ * K1 * K2) * ((Wf ![m 0, p] * SNorm Λ₁ Λ₂ (a ![m 0, p])) *
                (Wf ![m 1, m 2 - p] * SNorm Λ₁ 0 (b ![m 1, m 2 - p]))) := by simp only [hE]; ring
      _ = ∑' q : (Fin 3 → ℤ) × ℤ, FF (mergeEquiv q) :=
          (ENNReal.tsum_prod (f := fun m p => FF (mergeEquiv (m, p)))).symm
      _ = ∑' ab : (Fin 2 → ℤ) × (Fin 2 → ℤ), FF ab := mergeEquiv.tsum_eq FF
      _ = κ * K1 * K2 * ((∑' m, Wf m * SNorm Λ₁ Λ₂ (a m)) * (∑' m, Wf m * SNorm Λ₁ 0 (b m))) := by
          rw [ENNReal.tsum_prod (f := fun x y => FF (x, y))]
          simp only [FF]
          have : ∀ x : Fin 2 → ℤ, ∑' y : Fin 2 → ℤ, (κ * K1 * K2) * ((Wf x * SNorm Λ₁ Λ₂ (a x)) * (Wf y * SNorm Λ₁ 0 (b y))) =
              (κ * K1 * K2) * ((Wf x * SNorm Λ₁ Λ₂ (a x)) * ∑' y : Fin 2 → ℤ, Wf y * SNorm Λ₁ 0 (b y)) := fun x => by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
          simp_rw [this]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ ≤ κ * K1 * K2 * ((Cf * bf) * (Cg * bg)) := mul_le_mul' le_rfl (mul_le_mul' hab hbb)
  have hEfin : ∀ m : Fin 3 → ℤ, ∑' p : ℤ, E m p ≠ ⊤ := fun m => by
    refine ne_top_of_le_ne_top (b := κ * K1 * K2 * ((Cf * bf) * (Cg * bg))) ?_ ?_
    · exact ENNReal.mul_ne_top hKfin' (ENNReal.mul_ne_top habtop hbbtop)
    · exact le_trans (le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ0 (half m)))
        (le_trans (ENNReal.le_tsum (f := fun m : Fin 3 → ℤ => Wm m * ∑' p : ℤ, E m p) m) hTot)
  have hnu : ∀ r : Mom P.d, ‖r‖ ≤ 1 → ‖u • r‖ ≤ 1 := fun r hr => by
    rw [norm_smul, Real.norm_eq_abs]; nlinarith [abs_nonneg u, norm_nonneg r]
  have hterm : ∀ (r : Mom P.d), ‖r‖ ≤ 1 → ∀ (m : Fin 3 → ℤ) (p : ℤ),
      SNorm Λ₁ Λ₂ (fun k => a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) ≤ E m p := fun r hr m p => by
    have hG : SNorm Λ₁ 0 (b ![m 1, m 2 - p]) ≤ ENNReal.ofReal (SNorm Λ₁ 0 (b ![m 1, m 2 - p])).toReal :=
      le_of_eq (ENNReal.ofReal_toReal (hSb _)).symm
    have := snorm_shiftmulG_le hd hΛ (a ![m 0, p]) (b ![m 1, m 2 - p]) (u • r) (hnu r hr) ENNReal.toReal_nonneg (hSa _) hG
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (hSb _)]
    simp only [hE, hK1, hK2]
    ring
  have hcoef : ∀ (r : Mom P.d), ‖r‖ ≤ 1 → ∀ m : Fin 3 → ℤ,
      SNorm Λ₁ Λ₂ (fun k => ∑' p : ℤ, a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) ≤ K3 * ∑' p : ℤ, E m p := fun r hr m =>
    snorm_tsum_le hd hΛ (fun p k => a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) (E m) (hEfin m) (hterm r hr m)
  have hfs : coefBound (6 * P.η ^ 6) D.wN (rowOrder D (Sum.inl w₀))
      (fun m r k => cutW (fun r k => ∑' p : ℤ, a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) r k) ≤
      κ * K1 * K2 * K3 * Cf * Cg * bf * bg := by
    unfold coefBound
    rw [h1, h2]
    calc ∑' m : Fin 3 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) *
          ⨆ r : Mom P.d, SNorm Λ₁ Λ₂ (cutW (fun r k => ∑' p : ℤ, a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) r)
        ≤ ∑' m : Fin 3 → ℤ, K3 * (Wm m * ∑' p : ℤ, E m p) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          rw [mul_left_comm]
          exact mul_le_mul' le_rfl (snorm_cutW_le _ fun r hr => hcoef r hr m)
      _ = K3 * ∑' m : Fin 3 → ℤ, Wm m * ∑' p : ℤ, E m p := ENNReal.tsum_mul_left
      _ ≤ K3 * (κ * K1 * K2 * ((Cf * bf) * (Cg * bg))) := mul_le_mul' le_rfl hTot
      _ = κ * K1 * K2 * K3 * Cf * Cg * bf * bg := by ring
  have hbfin : κ * K1 * K2 * K3 * Cf * Cg * bf * bg ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hKfin hCf) hCg |> fun h => ENNReal.mul_ne_top h hbf) hbg
  refine ⟨RowData.ofModes (θ := 6 * P.η ^ 6) (Sum.inl w₀) s
    (fun m r k => cutW (fun r k => ∑' p : ℤ, a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) r k)
    (κ * K1 * K2 * K3 * Cf * Cg * bf * bg) hbfin hfs (fun w hw => absurd hw (by simp)),
    fun cl r k hr e1 e2 => RowData.ofModes_W (by
      have hHS := hasSum_merge a b (k + u • r) k (cl 0) (cl 1) (cl 2)
        (f ![cl 0, cl 2] (k + u • r)) (g ![cl 1, cl 2] k)
        (has _ e1 (k + u • r)) (hbs _ e2 k) (hnorma _) (hnormb _)
      have hclk : ![cl 0, cl 1, cl 2] = cl := by funext i; fin_cases i <;> rfl
      rw [hclk] at hHS
      show HasSum (fun m : Fin 3 → ℤ => cutW (fun r k => ∑' p : ℤ, a ![m 0, p] (k + u • r) * b ![m 1, m 2 - p] k) r k *
          fsPhase m cl) (f ![cl 0, cl 2] (k + u • r) * g ![cl 1, cl 2] k)
      simp only [cutW_of_le hr]
      exact hHS), fun _ => rfl,
    by show κ * K1 * K2 * K3 * Cf * Cg * bf * bg ≤ _
       simp only [mul_assoc]; exact le_of_eq (by ring), RowData.ofModes_ae hθ0 hI (Sum.inl w₀) _ _ _ _ _ _⟩

end WaveTurbulence.VineEstS5C.P4.W2

