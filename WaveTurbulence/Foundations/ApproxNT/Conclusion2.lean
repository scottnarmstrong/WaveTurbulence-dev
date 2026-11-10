/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep
public import WaveTurbulence.Foundations.ApproxNT.Conclusion1

/-!
# DH23 Prop 6.4, conclusion (2): the approximation `I_app` (packet NT6)

`|I_app| ≤ (λ₁⋯λ_n)^{2d} (C₁ C⁺ L^{2d-2γ} δ⁻¹)^n` and
`|I - I_app| ≤ (λ₁⋯λ_n)^{2d} (C₁ C⁺ L^{2d-2γ} δ⁻¹)^n L^{-γ₁+η}` (DH23 (conclusion2)), uniformly for
`n ≤ (log L)^A`, all `λ_j ≥ 1` and `L^{-η/2} ≤ δ ≤ 1` (FINDINGS F33, `GAP.largeOrder.nt`).

Proof: `|I - L^{2dn}∫WΨ|` is conclusion (1). For `L^{2dn}∫WΨ - I_app`, both are superpositions over
the cells `Q` and frequencies `τ` (`approxInt_cell`, `AppRep.singInt_eq`), and on one product of
cells the difference is bounded by `exists_app_cell_bound` (DH21 Lemma 6.3 for the `J`-factors, the
Hölder estimate for `Ψ̂₁` for the `J^c`-factors: DH21 Prop 6.1, L1648–L1657); `μ = L^{2γ}δ` makes
`μ⁻¹ + μ^{-(1-η/2)} ≤ 2 L^{-γ₁+η}`.
-/

public section

noncomputable section

open MeasureTheory Finset Filter
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

theorem poly_le_pow (n : ℕ) {c : ℝ} (hc : 1 ≤ c) : (n : ℝ) * (1 + 2 * n) * c ≤ (12 * c) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h2 : (1 : ℝ) + 2 * n ≤ 3 * 2 ^ n := by
      have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith
    have h3 : c ≤ c ^ n := le_self_pow₀ hc h.ne'
    have h4 : (3 : ℝ) ≤ 3 ^ n := le_self_pow₀ (by norm_num) h.ne'
    calc (n : ℝ) * (1 + 2 * n) * c ≤ 2 ^ n * (3 * 2 ^ n) * c ^ n := by gcongr
      _ ≤ 2 ^ n * (3 ^ n * 2 ^ n) * c ^ n := by gcongr
      _ = (12 * c) ^ n := by
          rw [show (12 : ℝ) * c = 2 * 3 * 2 * c by ring, mul_pow, mul_pow, mul_pow]; ring

theorem pow_add_poly_le (n : ℕ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 1 ≤ c) :
    a ^ n + (n : ℝ) * (1 + 2 * n) * c * b ^ n ≤ (a + 12 * c * b) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · calc a ^ n + (n : ℝ) * (1 + 2 * n) * c * b ^ n ≤ a ^ n + (12 * c) ^ n * b ^ n := by
          gcongr; exact poly_le_pow n hc
      _ = a ^ n + (12 * c * b) ^ n := by rw [mul_pow (12 * c) b]
      _ ≤ _ := pow_add_pow_le ha (by positivity) h.ne'

theorem gamma1_le_two_mul (d : ℕ) (γ : ℝ) : gamma1 d γ ≤ 2 * γ := min_le_left _ _

theorem gamma1_le_one (d : ℕ) (γ : ℝ) : gamma1 d γ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

/-- The scale `μ = L^{2γ}δ`: `μ > 1` and `μ⁻¹ + μ^{-(1-η/2)} ≤ 2 L^{-γ₁+η}`. -/
theorem mu_bounds {γ η L δ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηγ : η ≤ γ) (hL : 1 < L) (hδ : L ^ (-(η / 2)) ≤ δ) :
    1 < L ^ (2 * γ) * δ ∧
      (L ^ (2 * γ) * δ)⁻¹ + (L ^ (2 * γ) * δ) ^ (-(1 - η / 2)) ≤ 2 * L ^ (-gamma1 d γ + η) := by
  have hL0 : 0 < L := by linarith
  have hlow : L ^ (2 * γ - η / 2) ≤ L ^ (2 * γ) * δ := by
    rw [sub_eq_add_neg, Real.rpow_add hL0]
    exact mul_le_mul_of_nonneg_left hδ (Real.rpow_nonneg hL0.le _)
  have he : 0 < 2 * γ - η / 2 := by linarith
  have h1 : 1 < L ^ (2 * γ - η / 2) := Real.one_lt_rpow hL he
  have hμ1 : 1 < L ^ (2 * γ) * δ := h1.trans_le hlow
  refine ⟨hμ1, ?_⟩
  set μ := L ^ (2 * γ) * δ
  set θ := 1 - η / 2
  have hθ1 : θ ≤ 1 := by simp only [θ]; linarith
  have hθ0 : 0 ≤ θ := by simp only [θ]; linarith
  have hinv : μ⁻¹ ≤ μ ^ (-θ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hμ1.le (by linarith)
  have hθμ : μ ^ (-θ) ≤ (L ^ (2 * γ - η / 2)) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
  have hexp : -((2 * γ - η / 2) * θ) ≤ -gamma1 d γ + η := by
    have hg2 := gamma1_le_two_mul d γ
    have hg1 := gamma1_le_one d γ
    have hθ' : (2 * γ - η / 2) * θ ≥ 2 * γ - γ * η - η / 2 := by
      simp only [θ]; nlinarith
    rcases le_total γ (1 / 2) with hγ2 | hγ2
    · nlinarith
    · nlinarith
  have hL2 : (L ^ (2 * γ - η / 2)) ^ (-θ) ≤ L ^ (-gamma1 d γ + η) := by
    rw [← Real.rpow_mul hL0.le, mul_neg]
    exact Real.rpow_le_rpow_of_exponent_le hL.le hexp
  linarith

/-- The Fourier-side facts on `W` used by both conclusions. -/
theorem fourierW_setup {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ} {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWc : Continuous (Function.uncurry W))
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) {Cplus : ℝ}
    (hW : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal (Cplus ^ n))
    (hCp : 0 ≤ Cplus) :
    Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) ∧
    (∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ) ∧
    Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      ‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) ∧
    ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ Cplus ^ n := by
  have : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  set Q := (cellBox_finite hxs hys a b lam).toFinset
  have hWi : Integrable (Function.uncurry W) := by
    have hwc : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
        W z.1 z.2 * cellWeight pq z.1 z.2) := fun pq =>
      (hWc.mul (continuous_cellWeight pq)).integrable_of_hasCompactSupport
        (hasCompactSupport_cellWeight pq).mul_left
    refine (integrable_finsetSum Q fun pq _ => hwc pq).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry]
    exact (W_eq_sum_cells hxs hys hWs z.1 z.2).symm
  have hFc := continuous_fourierW hWi
  have hWlin : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ ≤
      ENNReal.ofReal (Cplus ^ n) := by
    refine le_trans (lintegral_mono fun τ => ?_) hW
    refine le_mul_of_one_le_right zero_le ?_
    rw [ENNReal.one_le_ofReal]
    have := freqNorm_nonneg τ.1 τ.2
    nlinarith [Real.pi_pos]
  have hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) :=
    ⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hWlin ENNReal.ofReal_lt_top⟩
  have hGi : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      ‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) := by
    refine ⟨(hFc.norm.mul (continuous_const.add (continuous_const.mul ?_))).aestronglyMeasurable,
      ?_⟩
    · exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
        (((continuous_apply j).comp continuous_fst).norm.pow 2).add
          (((continuous_apply j).comp continuous_snd).norm.pow 2))
    · refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hW ENNReal.ofReal_lt_top)
      refine lintegral_congr fun τ => ?_
      have hp : 0 ≤ 1 + 2 * Real.pi * freqNorm τ.1 τ.2 := by
        have := freqNorm_nonneg τ.1 τ.2; positivity
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hp),
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  refine ⟨hF, fun x y => fourierW_inversion hWc hWi hF x y, hGi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun τ => by
    have := freqNorm_nonneg τ.1 τ.2; positivity) hGi.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) hW)
  refine lintegral_congr fun τ => ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]

/-- The base case of the cell representation of `I_app`. -/
theorem W_eq_sum_appFac {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ} {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam)
    (hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ) (J : Finset (Fin n))
    (x y : Fin n → Mom d) :
    W x y = ∑ pq ∈ (cellBox_finite hxs hys a b lam).toFinset,
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 * ∏ j, appFac J 0 pq τ x y j := by
  conv_lhs => rw [W_eq_sum_cells hxs hys hWs x y]
  refine sum_congr rfl fun pq _ => ?_
  rw [hinv x y, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h := multiAmp_cellData pq τ (fun j => (x j, y j))
  have hprod : ∏ j, appFac J 0 pq τ x y j = multiAmp (cellData pq τ).p (cellData pq τ).q
      (cellData pq τ).ξ (cellData pq τ).ζ (fun j => (x j, y j)) := by
    have hj : ∀ j : Fin n, ¬ (n ≤ (j : ℕ) + 0) := fun j => by have := j.isLt; omega
    simp only [appFac, hj, ↓reduceIte, multiAmp, cellFn, cellData]
  simp only at h ⊢
  rw [hprod, h, mul_assoc]

/-- **DH23 Prop 6.4, conclusion (2)** (`Revision_Submit.tex` L1004–L1010; proof as DH21 Prop 6.1,
`Inventiones-Final_Version.tex` L1504–L1657), uniformly for orders `n ≤ (log L)^A` and arbitrary
box sizes `λ_j ≥ 1` (FINDINGS F33, `GAP.largeOrder.nt`).

`I_app` is `approxApp L δ γ J Ψ₁ W` (DH23 (intappr): `p.v.` as the limit of the `χ_∞(ν⟨x,y⟩)`
truncations, `δ(⟨x,y⟩)` in the hyperplane reading of ruling D6, integrated one pair `(x_j, y_j)`
at a time, backwards from `j = n-1` as in DH21 L1636). Hypotheses as in `approxnt_conclusion1`,
plus the second half of (propertypsi2), `‖max_{j∈J^c} ⟨Ω_j⟩^{1-η/2} Ψ₁‖_{L¹} ≤ C₀^n`; the source's
`δ` is a fixed constant and `L` is large depending on `δ` (DH23 L438), made quantitative here by
`L^{-η/2} ≤ δ ≤ 1`; and `η ≤ γ` (part of "`η ≪_{d,γ} 1`", DH23 L438). -/
theorem approxnt_conclusion2 (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) (hηγ' : η ≤ γ) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, L ^ (-(η / 2)) ≤ δ →
      δ ≤ 1 → ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A → ∀ Cplus : ℝ, 0 ≤ Cplus →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
          ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal (Cplus ^ n) →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∫⁻ Ω, ENNReal.ofReal (wmax (1 - η / 2) (fun i => Ω i)) * ‖Ψ₁ Ω‖ₑ ≤
        ENNReal.ofReal (C₀ ^ n) →
      ‖approxApp L δ γ J Ψ₁ W‖ ≤
          (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n ∧
      ‖approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) - approxApp L δ γ J Ψ₁ W‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) := by
  obtain ⟨C₁', hC₁', hconc1⟩ := approxnt_conclusion1 hd hγ hη0 hη hηγ hC₀
  obtain ⟨Ka, hKa, hcell⟩ := exists_app_cell_bound hd
  set c : ℝ := 2 * (1 + 4 * Real.pi)
  have hc : 1 ≤ c := by simp only [c]; nlinarith [Real.pi_pos]
  set K₂ : ℝ := (7 : ℝ) ^ (2 * d) * Ka * C₀
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨C₁' + 12 * c * K₂, by positivity, fun A => ?_⟩
  obtain ⟨L₀', hL₀'⟩ := hconc1 A
  refine ⟨max L₀' 2, fun L hL δ hδ hδ1 n hn Cplus hCp lt _ xs ys hxs hys a b lam hlam W hWc hWs
    hW J Ψ₁ hΨ hD hH => ?_⟩
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hδ
  have : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  obtain ⟨hμ1, hμe⟩ := mu_bounds (d := d) hη0 (by linarith) hηγ' (by linarith) hδ
  set μ := L ^ (2 * γ) * δ with hμdef
  have hμ0 : 0 < μ := by linarith
  set Q := (cellBox_finite hxs hys a b lam).toFinset
  set Ψ := resProfile J Ψ₁
  set e : ℝ := L ^ (-gamma1 d γ + η)
  have he0 : 0 ≤ e := Real.rpow_nonneg hL0.le _
  set X : ℝ := L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.2 hδ0.le)
  have hXμ : L ^ (2 * d) / μ = X := Lpow_div_mu hL0
  have hprod0 : 0 ≤ ∏ j, lam j := prod_nonneg fun j _ => by linarith [hlam j]
  obtain ⟨hF, hinv, hGi, hGint⟩ := fourierW_setup hxs hys hWc hWs hW hCp
  have hFint : ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ ≤ Cplus ^ n := by
    refine le_trans (integral_mono hF.norm hGi fun τ => ?_) hGint
    have := freqNorm_nonneg τ.1 τ.2
    have hπ := Real.pi_pos
    exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith)
  -- the profile bounds
  have hD0 : ∀ k, 0 ≤ C₀ ^ n * ((4 * k).factorial : ℝ) := fun k => by positivity
  have hΨ1 : ∫ Ω, ‖Ψ₁ Ω‖ ≤ C₀ ^ n := by
    have h := integral_norm_wordDeriv_le hΨ hD hD0 (k := 0) Fin.elim0
    simp only [mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one] at h
    refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) h
    simp [wordDeriv, iteratedFDeriv_zero_apply]
  -- the target term of one cell
  set tgt : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → (Fin n → Mom d) × (Fin n → Mom d) → ℂ :=
    fun pq τ => (L : ℂ) ^ (2 * d * n) * ((μ⁻¹ : ℂ) ^ n * (∫ Ω, Ψ₁ Ω) *
      ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)) with htgt
  have hLn : ‖(L : ℂ) ^ (2 * d * n)‖ = (L ^ (2 * d)) ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hL0.le, pow_mul]
  have hKX : (L ^ (2 * d)) ^ n * (Ka / μ) ^ n * C₀ ^ n = (Ka * C₀ * X) ^ n := by
    rw [← hXμ, ← mul_pow, ← mul_pow]; congr 1; field_simp
  have hcellK : ∀ (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin n),
      μ * ((‖NTSP.intVec (pq j).1‖ + Real.sqrt d) *
      (‖NTSP.intVec (pq j).2‖ + Real.sqrt d)) ≤ 2 ^ cellLevels μ pq j := fun pq j =>
    (Nat.le_ceil _).trans (by
      have := (Nat.lt_two_pow_self (n := cellLevels μ pq j)).le
      exact_mod_cast this)
  have hcellb := fun pq (τ : (Fin n → Mom d) × (Fin n → Mom d)) =>
    hcell J (cellLevels μ pq) Ψ₁ _ hΨ hD hD0 (C₀ ^ n) hΨ1 (1 - η / 2) (C₀ ^ n)
      (by linarith) (by linarith) (by positivity) hH μ hμ1 (cellData pq τ) (hcellK pq)
  have htgt_le : ∀ pq τ, ‖tgt pq τ‖ ≤ (Ka * C₀ * X) ^ n := fun pq τ => by
    have h := (hcellb pq τ).2
    rw [Fintype.card_fin] at h
    simp only [htgt]
    rw [norm_mul, hLn, ← hKX, mul_assoc ((L ^ (2 * d)) ^ n)]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have htgt_m : ∀ pq, AEStronglyMeasurable (tgt pq) := fun pq => by
    refine (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul ?_))
    refine (Finset.stronglyMeasurable_fun_prod _ fun j _ => ?_).aestronglyMeasurable
    have hτ : Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => (τ.1 j, τ.2 j)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    have h := (stronglyMeasurable_cellOp hd J j (NTSP.intVec (pq j).1)
      (NTSP.intVec (pq j).2)).comp_measurable hτ
    exact h
  have htgt_i : ∀ pq, Integrable (fun τ => fourierW W τ.1 τ.2 * tgt pq τ) := fun pq =>
    hF.mul_bdd (htgt_m pq) (Filter.Eventually.of_forall fun τ => htgt_le pq τ)
  -- `I_app` as a superposition
  have hIapp : approxApp L δ γ J Ψ₁ W = ∑ pq ∈ Q, ∫ τ, fourierW W τ.1 τ.2 * tgt pq τ := by
    rw [approxApp, singInt_eq hd J Q hF (W_eq_sum_appFac hxs hys hWs hinv J), mul_sum]
    refine sum_congr rfl fun pq _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [htgt]
    have hc1 : ((X : ℝ) : ℂ) ^ n = (L : ℂ) ^ (2 * d * n) * (μ⁻¹ : ℂ) ^ n := by
      rw [← hXμ, div_eq_mul_inv, Complex.ofReal_mul, mul_pow, Complex.ofReal_inv,
        ← complex_Lpow (n := n) L]
    simp only [X] at hc1
    rw [hc1]
    ring
  -- the integral `L^{2dn} ∫ W Ψ` as a superposition
  have hhm : ∀ pq, Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) := fun pq =>
    (continuous_cellWeight pq).mul ((continuous_resProfile J hΨ.continuous).comp
      (continuous_pi fun j => continuous_const.mul
        (((continuous_apply j).comp continuous_fst).inner ((continuous_apply j).comp continuous_snd))))
  have hhs : ∀ pq, HasCompactSupport (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (hasCompactSupport_cellWeight pq).mul_right
  have hh : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (hhm pq).integrable_of_hasCompactSupport (hhs pq)
  have hcelli : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      W z.1 z.2 * cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) := by
    intro pq
    have hc : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
        W z.1 z.2 * (cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) :=
      hWc.mul (hhm pq)
    exact (hc.integrable_of_hasCompactSupport (hhs pq).mul_left).congr
      (Filter.Eventually.of_forall fun z => by simp only [mul_assoc])
  have hInt : (L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ - approxApp L δ γ J Ψ₁ W =
      ∑ pq ∈ Q, ∫ τ, fourierW W τ.1 τ.2 * ((L : ℂ) ^ (2 * d * n) *
        multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
          (cellData pq τ).ξ (cellData pq τ).ζ - tgt pq τ) := by
    rw [approxInt_eq_sum_cells hxs hys hWs μ Ψ hcelli, hIapp, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun pq _ => ?_
    obtain ⟨hTi, hTeq⟩ := approxInt_cell μ hinv hF Ψ pq (hh pq) (hhm pq)
    rw [hTeq, ← integral_const_mul, ← integral_sub (hTi.const_mul _) (htgt_i pq)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [multiInt_res_eq_trunc hμ0.le J Ψ₁ pq τ]
    ring
  -- the bound on one cell
  have hτb : ∀ pq (τ : (Fin n → Mom d) × (Fin n → Mom d)),
      ‖(L : ℂ) ^ (2 * d * n) * multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p
        (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ - tgt pq τ‖ ≤
      (Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e *
        (1 + 2 * Real.pi * freqNorm τ.1 τ.2) := fun pq τ => by
    have h := (hcellb pq τ).1
    rw [Fintype.card_fin] at h
    simp only [htgt]
    rw [← mul_sub, norm_mul, hLn]
    set S := ∑ j, (‖(cellData pq τ).ξ j‖ + ‖(cellData pq τ).ζ j‖)
    have hF0 := freqNorm_nonneg τ.1 τ.2
    have hS : 1 + S ≤ (1 + 2 * n) * (1 + 2 * Real.pi * freqNorm τ.1 τ.2) := by
      have h1 : S ≤ 2 * n * freqNorm τ.1 τ.2 := by
        have h2 : S ≤ ∑ _j : Fin n, 2 * freqNorm τ.1 τ.2 :=
          sum_le_sum fun j _ => (add_le_add (norm_le_freqNorm_fst τ.1 τ.2 j)
            (norm_le_freqNorm_snd τ.1 τ.2 j)).trans (le_of_eq (two_mul _).symm)
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
        exact h2.trans (le_of_eq (by ring))
      have hπ := Real.pi_gt_three
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have h3 : 0 ≤ (n : ℝ) * freqNorm τ.1 τ.2 := mul_nonneg hn0 hF0
      have h4 := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 4 * Real.pi) h3
      have h5 : 0 ≤ Real.pi * freqNorm τ.1 τ.2 := mul_nonneg Real.pi_pos.le hF0
      linarith only [h1, h4, h5, hn0]
    have hS0 : 0 ≤ S := sum_nonneg fun _ _ => by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (L ^ (2 * d)) ^ n * ‖multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p
          (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ - (μ⁻¹ : ℂ) ^ n *
            (∫ Ω, Ψ₁ Ω) * ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)
              (τ.1 j) (τ.2 j)‖
        ≤ (L ^ (2 * d)) ^ n * ((Ka / μ) ^ n * ((C₀ ^ n + 4 * Real.pi * C₀ ^ n) * n * (1 + S) *
            (μ⁻¹ + μ ^ (-(1 - η / 2))))) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (L ^ (2 * d)) ^ n * (Ka / μ) ^ n * C₀ ^ n * ((1 + 4 * Real.pi) * n * (1 + S) *
            (μ⁻¹ + μ ^ (-(1 - η / 2)))) := by ring
      _ ≤ (Ka * C₀ * X) ^ n * ((1 + 4 * Real.pi) * n * ((1 + 2 * n) *
            (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) * (2 * e)) := by
          rw [hKX]
          gcongr
      _ = _ := by simp only [c]; ring
  have hpqb : ∀ pq, ‖∫ τ, fourierW W τ.1 τ.2 * ((L : ℂ) ^ (2 * d * n) *
      multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ - tgt pq τ)‖ ≤
      (Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e * Cplus ^ n := by
    intro pq
    have hk : 0 ≤ (Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e := by positivity
    refine (norm_integral_le_of_norm_le
      (hGi.const_mul ((Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e))
      (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
    · rw [norm_mul]
      calc ‖fourierW W τ.1 τ.2‖ * ‖(L : ℂ) ^ (2 * d * n) * multiInt μ
            (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
            (cellData pq τ).ξ (cellData pq τ).ζ - tgt pq τ‖
          ≤ ‖fourierW W τ.1 τ.2‖ * ((Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e *
              (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) :=
            mul_le_mul_of_nonneg_left (hτb pq τ) (norm_nonneg _)
        _ = _ := by ring
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hGint hk
  have hcard := card_cells_le hxs hys a b hlam
  have h7 : (7 : ℝ) ^ (2 * d * n) * (Ka * C₀ * X) ^ n = (K₂ * X) ^ n := by
    rw [pow_mul, ← mul_pow]; simp only [K₂]; ring
  refine ⟨?_, ?_⟩
  · -- `|I_app|`
    rw [hIapp]
    calc ‖∑ pq ∈ Q, ∫ τ, fourierW W τ.1 τ.2 * tgt pq τ‖
        ≤ ∑ _pq ∈ Q, (Ka * C₀ * X) ^ n * Cplus ^ n := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun pq _ => ?_)
          refine (norm_integral_le_of_norm_le (hF.norm.mul_const ((Ka * C₀ * X) ^ n))
            (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (htgt_le pq τ) (norm_nonneg _)
          · rw [integral_mul_const, mul_comm]
            exact mul_le_mul_of_nonneg_left hFint (by positivity)
      _ = Q.card * ((Ka * C₀ * X) ^ n * Cplus ^ n) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) * ((Ka * C₀ * X) ^ n * Cplus ^ n) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (∏ j, lam j) ^ (2 * d) * (K₂ * Cplus * X) ^ n := by
          rw [show (K₂ * Cplus * X) ^ n = (K₂ * X) ^ n * Cplus ^ n by ring, ← h7]; ring
      _ ≤ (∏ j, lam j) ^ (2 * d) * ((C₁' + 12 * c * K₂) * Cplus * X) ^ n := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ n) (by positivity)
          have : K₂ ≤ C₁' + 12 * c * K₂ := by
            have h12 : K₂ ≤ 12 * c * K₂ := le_mul_of_one_le_left hK₂ (by linarith only [hc])
            linarith only [h12, hC₁']
          gcongr
      _ = _ := by simp only [X]; ring
  · -- `|I - I_app|`
    have h1 := hL₀' L ((le_max_left _ _).trans hL) δ ⟨hδ0, hδ1⟩ n hn Cplus hCp lt xs ys hxs hys a b
      lam hlam W hWc hWs hW J Ψ₁ hΨ hD
    have hsplit : approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) - approxApp L δ γ J Ψ₁ W =
        (approxSum L μ W Ψ - (L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ) +
          ((L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ - approxApp L δ γ J Ψ₁ W) := by ring
    rw [hsplit]
    have h2 : ‖(L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ - approxApp L δ γ J Ψ₁ W‖ ≤
        (∏ j, lam j) ^ (2 * d) * e * ((n : ℝ) * (1 + 2 * n) * c * (K₂ * Cplus * X) ^ n) := by
      rw [hInt]
      calc ‖∑ pq ∈ Q, ∫ τ, fourierW W τ.1 τ.2 * ((L : ℂ) ^ (2 * d * n) *
            multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
              (cellData pq τ).ξ (cellData pq τ).ζ - tgt pq τ)‖
          ≤ ∑ _pq ∈ Q, (Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e * Cplus ^ n :=
            (norm_sum_le _ _).trans (sum_le_sum fun pq _ => hpqb pq)
        _ = Q.card * ((Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e * Cplus ^ n) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) *
              ((Ka * C₀ * X) ^ n * ((n : ℝ) * (1 + 2 * n) * c) * e * Cplus ^ n) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
            rw [show (K₂ * Cplus * X) ^ n = (K₂ * X) ^ n * Cplus ^ n by ring, ← h7]; ring
    have hC1 : (C₁' * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n = (C₁' * Cplus * X) ^ n := by
      simp only [X]; ring
    rw [hC1] at h1
    calc ‖(approxSum L μ W Ψ - (L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ) +
          ((L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ - approxApp L δ γ J Ψ₁ W)‖
        ≤ (∏ j, lam j) ^ (2 * d) * (C₁' * Cplus * X) ^ n * e +
            (∏ j, lam j) ^ (2 * d) * e * ((n : ℝ) * (1 + 2 * n) * c * (K₂ * Cplus * X) ^ n) :=
          (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = (∏ j, lam j) ^ (2 * d) * e * ((C₁' * Cplus * X) ^ n +
            (n : ℝ) * (1 + 2 * n) * c * (K₂ * Cplus * X) ^ n) := by ring
      _ ≤ (∏ j, lam j) ^ (2 * d) * e * (C₁' * Cplus * X + 12 * c * (K₂ * Cplus * X)) ^ n :=
          mul_le_mul_of_nonneg_left (pow_add_poly_le n (by positivity) (by positivity) hc)
            (by positivity)
      _ = _ := by simp only [X, e]; ring

end WaveTurbulence.ApproxNT
