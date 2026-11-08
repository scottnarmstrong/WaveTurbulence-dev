/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickRep
public import WaveTurbulence.Foundations.Flower.FiltCoh.CrudeSum

/-! # FILT-COH (d2b): the modulation-uniform crude NT sum with resonance filters (o82 Thm 10.1 (10.5), Prop 15.1)

* `exists_crude_cell_of_rep`: the crude core estimate (`exists_crude_core_bound`) for ANY profile with a weighted
  Fourier representation of the cell shape `Z^n · c^{|F|}`: `‖multiSum‖ ≤ 2 (K Z L^{2d}/μ)^n`;
* `crude_sum_of_cells`: main's cell decomposition (`approxSum_eq_sum_cells`, `approxSum_cell`) turns a uniform cell
  bound into the bound of the localized lattice sum (only the Fourier MASS of the amplitude enters);
* `halfCell_crude_filt`, `halfCell_crude_filt_res`: the actual normalized half-cell sum with the filtered profile
  `filtRes J Ψ₁ ψ` (every `ψ_j` a product of at most `N` good factors), uniformly in the modulations:
  `≤ 2 (C δ/4)^n`.

Proofs adapted from FiltCoh's `exists_filt_crude_cell_bound`, `filt_crude_sum_uniform`, `halfCell_crude_uniform`,
`halfCell_crude_uniform_res` (CrudeCore/CrudeSum, this area). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory WaveTurbulence.ApproxNT WaveTurbulence.RegAsymp Finset Set
open WaveTurbulence.Flower.FiltNT WaveTurbulence.Incoh
open scoped ENNReal ContDiff FourierTransform

variable {d : ℕ}

/-- **The crude cell estimate for a represented profile.** -/
theorem exists_crude_cell_of_rep (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η → δ ∈ Ioc (0 : ℝ) 1 →
      (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ≤ 1 / 2 →
      ∀ (Φ Φh : (Fin n → ℝ) → ℂ), IsFourierRep Φ Φh → ∀ Z : ℝ, 0 ≤ Z →
      (∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤
        Z ^ n * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card) →
      ∀ c : CellData d (Fin n),
      ‖multiSum L (δ * L ^ (2 * γ)) Φ c.p c.q c.ξ c.ζ‖ ≤ 2 * (K * Z * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by
  obtain ⟨K, hK0, hcore⟩ := exists_crude_core_bound hd hγ hη0 hη
  refine ⟨K, hK0, ?_⟩
  intro n L δ hL hLη hδ hnq Φ Φh hrep Z hZ hA c
  have hL0 : 0 < L := by linarith
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  set ε : ℝ := L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)
  have hε : 0 ≤ ε := Real.rpow_nonneg hL0.le _
  set q : ℝ := 2 ^ (d + 1) * B ^ (8 * d) * ε
  have hq : 0 ≤ q := by positivity
  set A : Finset (Fin n) → ℝ := fun F => Z ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card
  have h := hcore (Fin n) L δ hL hLη hδ Φ Φh hrep A hA c
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have hsum : ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card ≤ Z ^ n * 2 := by
    have h1 : ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card =
        Z ^ n * ∑ F ∈ (univ : Finset (Fin n)).powerset, q ^ F.card := by
      rw [mul_sum]
      refine sum_congr rfl fun F _ => ?_
      simp only [A, q, mul_pow]; ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := sum_powerset_erase_pow_le (ι := Fin n) hq (by simpa [q] using hnq)
    rw [← add_sum_erase _ _ (empty_mem_powerset _), Finset.card_empty, pow_zero]
    simp only [Fintype.card_fin] at h2
    have h3 : 2 * (n : ℝ) * q ≤ 1 := by
      have : (n : ℝ) * q ≤ 1 / 2 := hnq
      linarith
    linarith
  have hx : 0 ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by
    have := hδ.1; positivity
  calc (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card
      ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n * (Z ^ n * 2) :=
        mul_le_mul_of_nonneg_left hsum hx
    _ = _ := by rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow]; ring

/-- **A uniform cell bound gives the localized lattice-sum bound** (main's cell decomposition). -/
theorem crude_sum_of_cells {n : ℕ} {L : ℝ} (hL0 : 0 < L) (μ : ℝ) {Cplus : ℝ} (hCp : 0 ≤ Cplus)
    (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n)
    (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    (a b : Fin n → Mom d) (lam : Fin n → ℝ) (hlam : ∀ j, 1 ≤ lam j)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (hWc : Continuous (Function.uncurry W))
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam)
    (hW : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ ≤ ENNReal.ofReal (Cplus ^ n))
    (Ψ : (Fin n → ℝ) → ℂ) {X : ℝ} (hX0 : 0 ≤ X)
    (hcell : ∀ c : CellData d (Fin n), ‖multiSum L μ Ψ c.p c.q c.ξ c.ζ‖ ≤ 2 * X ^ n) :
    ‖approxSum L μ W Ψ‖ ≤ 2 * (∏ j, lam j) ^ (2 * d) * ((7 : ℝ) ^ (2 * d) * X * Cplus) ^ n := by
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
  have hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) :=
    ⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hW ENNReal.ofReal_lt_top⟩
  have hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ :=
    fun x y => fourierW_inversion hWc hWi hF x y
  have hGint : ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ ≤ Cplus ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun τ => norm_nonneg _)
      hF.norm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) hW)
    exact lintegral_congr fun τ => ofReal_norm _
  have hcellb : ∀ pq, ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
      multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤
        2 * X ^ n * Cplus ^ n := by
    intro pq
    refine (norm_integral_le_of_norm_le (hF.norm.const_mul (2 * X ^ n))
      (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
    · rw [norm_mul, mul_comm (2 * X ^ n)]
      exact mul_le_mul_of_nonneg_left (hcell (cellData pq τ)) (norm_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hGint (by positivity)
  have hdec : approxSum L μ W Ψ =
      ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ := by
    rw [approxSum_eq_sum_cells hxs hys hWs hL0 μ Ψ]
    exact sum_congr rfl fun pq _ => approxSum_cell hL0 μ hinv hF Ψ pq
  rw [hdec]
  calc ‖∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖
      ≤ ∑ _pq ∈ Q, 2 * X ^ n * Cplus ^ n :=
        (norm_sum_le _ _).trans (sum_le_sum fun pq _ => hcellb pq)
    _ = Q.card * (2 * X ^ n * Cplus ^ n) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) * (2 * X ^ n * Cplus ^ n) :=
        mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ = 2 * (∏ j, lam j) ^ (2 * d) * ((7 : ℝ) ^ (2 * d) * X * Cplus) ^ n := by
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm (2 * d) n, pow_mul]
        ring

/-- The filtered pole profile times the link filters is represented, with the cell weight shape. -/
theorem exists_filt_rep (hd1 : 1 ≤ d) {n : ℕ} (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    {K : ℝ} (hK : 1 ≤ K) (N : ℕ) (J : Finset (Fin n)) (S : Fin n → ℝ) (hS : ∀ j, 1 ≤ S j)
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (hΨ : ContDiff ℝ ∞ Ψ₁)
    (hD : WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)))
    (ψ : Fin n → ℝ → ℂ) (hψ : ∀ j, FiltMul d K N (ψ j)) :
    ∃ Φh : (Fin n → ℝ) → ℂ, IsFourierRep (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j)) Φh ∧
      ∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤
        ((2 ^ d * K) ^ N * max 1 Kp * C₀) ^ n *
          (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card := by
  have hD0 : ∀ k, 0 ≤ C₀ ^ n * ((4 * k).factorial : ℝ) := fun k => by
    have : 0 ≤ C₀ := by linarith
    positivity
  have hrep := isFourierRep_filtProf hd1 J S hS hΨ hD hD0
  set A : Finset (Fin n) → ℝ := fun F => max 1 Kp ^ n * C₀ ^ n *
    (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card
  have hA : ∀ F s, ‖filtHat J S Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F := fun F s =>
    (norm_filtHat_mul_le J S Kp hKp (fun j s' => hb (S j) (hS j) s') hΨ hD hD0 F s).trans
      (filt_weight_le J Kp hKp hC₀ F)
  obtain ⟨Φh, hrep', hA'⟩ := exists_rep_mul_filtMul hK hrep A hA N ψ hψ univ
  refine ⟨Φh, isFourierRep_congr (fun Ω => rfl) hrep', fun F s => (hA' F s).trans (le_of_eq ?_)⟩
  rw [card_univ, Fintype.card_fin, pow_mul]
  simp only [A, mul_pow]
  ring

/-- **The actual half-cell sum with the filtered pole and link filters, uniform in the modulations.** -/
theorem halfCell_crude_filt (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1) (hη0 : 0 < η)
    (hη : η ≤ 1/20) (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
        WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
      ∀ ψ : Fin n → ℝ → ℂ, (∀ j, FiltMul d K N (ψ j)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ')
            (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j))‖ ≤ 2*(C*δ/4)^n := by
  obtain ⟨Kp, hKp, hb⟩ := filtPole_bound d (by omega)
  obtain ⟨Kc, hKc0, hcell⟩ := exists_crude_cell_of_rep hd hγ (η := η / 4) (by positivity) (by linarith)
  set Z : ℝ := (2 ^ d * K) ^ N * max 1 Kp * C₀ with hZ
  have hZ0 : 0 ≤ Z := by
    have : 0 ≤ max 1 Kp := le_trans zero_le_one (le_max_left _ _)
    have : 0 ≤ K := by linarith
    have : 0 ≤ C₀ := by linarith
    positivity
  set r : ℝ := max 1 (Real.sqrt d)
  set D : ℝ := halfLinkFirstMomentConstant d
  have hr : 1 ≤ r := le_max_left _ _
  have hD : 0 < D := halfLinkFirstMomentConstant_pos d
  set C₁ : ℝ := (7 : ℝ) ^ (2 * d) * (Kc * Z + 1) with hC₁
  refine ⟨C₁ * D ^ 2 * r ^ (2 * d), by positivity, fun A => ?_⟩
  have hgap : 3 * η / 4 < 2 * ((d : ℝ) - 1) * (1 - γ) := by
    have h1 : 0 < ((d : ℝ) - 1) * (1 - γ) :=
      mul_pos (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) (by linarith [hγ.2])
    nlinarith
  obtain ⟨L₀, hL₀⟩ := exists_large_L (by omega : 1 ≤ d) hη0 hgap A
  refine ⟨max L₀ 2, fun L hL δ hδ n hn z β γ' J S hS Ψ₁ hΨ hDer ψ hψ => ?_⟩
  obtain ⟨hL2, hLη, hpoly, hsmall⟩ := hL₀ L ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := by linarith
  have hδ0 := hδ.1
  set μ := L ^ (2 * γ) * δ with hμdef
  have hμ' : μ = δ * L ^ (2 * γ) := mul_comm _ _
  have hμ0 : 0 < μ := mul_pos (Real.rpow_pos_of_pos hL0 _) hδ0
  -- the per-cell bound
  have hnq : (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
      L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) ≤ 1 / 2 := by
    have hp := hpoly n hn
    calc (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
          L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) =
          2 ^ (d + 1) * ((n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) *
          L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by ring
      _ ≤ 2 ^ (d + 1) * L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by
          gcongr
      _ ≤ 1 / 2 := hsmall
  obtain ⟨Φh, hrep, hA⟩ := exists_filt_rep (by omega) Kp hKp hb hC₀ hK N J S hS Ψ₁ hΨ hDer ψ hψ
  set X : ℝ := Kc * Z * L ^ (2 * d) / μ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hcb : ∀ c : CellData d (Fin n), ‖multiSum L μ (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j))
      c.p c.q c.ξ c.ζ‖ ≤ 2 * X ^ n := by
    intro c
    have h := hcell n L δ hL2 hLη hδ hnq _ Φh hrep Z hZ0 hA c
    rw [← hμ'] at h
    exact h
  have hmass : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ') τ.1 τ.2‖ₑ ≤ ENNReal.ofReal ((D ^ 2) ^ n) := by
    rw [← pow_mul]; exact halfCellAmplitude_fourier_mass z β γ'
  have hh := crude_sum_of_cells hL0 μ (by positivity : (0:ℝ) ≤ D ^ 2) (fun i j : Fin n => i<j)
    (fun _ => .zero) (fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
    (fun _ => r) (fun _ => hr) (halfCellAmplitude z β γ')
    (continuous_halfCellAmplitude z β γ') (halfCellAmplitude_support z β γ') hmass _ hX0 hcb
  have hY : X = Kc * Z * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) := by
    simp only [X]; rw [mul_div_assoc, Lpow_div_mu hL0]
  have hLY : 0 ≤ L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.2 hδ0.le)
  have hh' : ‖approxSum L μ (halfCellAmplitude z β γ') (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j))‖ ≤
      2 * (∏ _j : Fin n, r) ^ (2 * d) * (C₁ * D ^ 2 * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n := by
    refine hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ n) (by positivity))
    rw [hY]
    simp only [C₁]
    have : Kc * Z ≤ Kc * Z + 1 := by linarith
    calc (7 : ℝ) ^ (2 * d) * (Kc * Z * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * D ^ 2
        ≤ (7 : ℝ) ^ (2 * d) * ((Kc * Z + 1) * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * D ^ 2 := by gcongr
      _ = _ := by ring
  set q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq]
  have hs := normalized_scale (γ := γ) n d hL0 hδ0.ne' (C₁*D^2)
  calc q * ‖approxSum L μ (halfCellAmplitude z β γ') (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j))‖
      ≤ q * (2 * (∏ _j : Fin n, r) ^ (2 * d) * (C₁ * D ^ 2 * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n) :=
        mul_le_mul_of_nonneg_left hh' hq
    _ = 2 * (∏ _j : Fin n, r) ^ (2 * d) * (q * (C₁ * D ^ 2 * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n) := by
        ring
    _ = 2 * ((C₁ * D ^ 2 * r ^ (2 * d)) * δ / 4) ^ n := by
        rw [hs]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [show (C₁ * D ^ 2 * r ^ (2 * d)) * δ / 4 = r ^ (2 * d) * (C₁ * D ^ 2 * δ / 4) by ring,
          mul_pow, ← pow_mul, ← pow_mul, mul_comm n (2 * d)]
        ring

/-- On the support of a localized amplitude, the unfiltered pole may be replaced by the filtered one, with any
extra profile factor. -/
theorem approxSum_filtRes_eq {n : ℕ} (L μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (ψ : Fin n → ℝ → ℂ) (S : Fin n → ℝ)
    (hS : ∀ j, 0 < S j)
    (hsupp : ∀ x y, W x y ≠ 0 → ∀ j, |μ * inner ℝ (x j) (y j)| ≤ S j / 2) :
    approxSum L μ W (filtRes J Ψ₁ ψ) = approxSum L μ W (fun Ω => filtProf J S Ψ₁ Ω * ∏ j, ψ j (Ω j)) := by
  unfold approxSum
  refine tsum_congr fun g => ?_
  by_cases hW : W (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  unfold filtRes resProfile filtProf
  congr 2
  refine prod_congr rfl fun j _ => ?_
  have h := hsupp _ _ hW j
  have hu : |μ * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)) / S j| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (hS j), div_le_iff₀ (hS j)]; linarith
  simp only [gS, Fourier.chi0_eq_one hu, mul_one]

/-- **The actual half-cell sum with the unfiltered pole and link filters, uniform in the modulations.** -/
theorem halfCell_crude_filt_res (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1) (hη0 : 0 < η)
    (hη : η ≤ 1/20) (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
        WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
      ∀ ψ : Fin n → ℝ → ℂ, (∀ j, FiltMul d K N (ψ j)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (filtRes J Ψ₁ ψ)‖ ≤ 2*(C*δ/4)^n := by
  obtain ⟨C, hC, hNT⟩ := halfCell_crude_filt hd hγ hη0 hη hηγ hC₀ hK N
  refine ⟨C, hC, fun A => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hNT A
  refine ⟨L₀, fun L hL δ hδ n hn z β γ' J Ψ₁ hΨ hDer ψ hψ => ?_⟩
  set r : ℝ := max 1 (Real.sqrt d)
  set μ := L^(2*γ)*δ
  set S : Fin n → ℝ := fun j =>
    2 * (|μ| * ((‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r))) + 2
  have hr0 : 0 ≤ r := le_trans zero_le_one (le_max_left _ _)
  have hS1 : ∀ j, 1 ≤ S j := fun j => by
    have : 0 ≤ |μ| * ((‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r)) := by positivity
    simp only [S]; linarith
  have hsupp : ∀ x y, halfCellAmplitude z β γ' x y ≠ 0 → ∀ j, |μ * inner ℝ (x j) (y j)| ≤ S j / 2 := by
    intro x y hW j
    have hs := halfCellAmplitude_support z β γ' x y hW j
    simp only [Shift.eval, add_zero] at hs
    have hx : ‖x j‖ ≤ ‖halfCellCenter (z (j,0))‖ + r := by
      have := norm_le_norm_add_norm_sub' (x j) (halfCellCenter (z (j,0)))
      linarith [hs.1]
    have hy : ‖y j‖ ≤ ‖halfCellCenter (z (j,1))‖ + r := by
      have := norm_le_norm_add_norm_sub' (y j) (halfCellCenter (z (j,1)))
      linarith [hs.2]
    rw [abs_mul]
    have hi := abs_real_inner_le_norm (x j) (y j)
    have h1 : |inner ℝ (x j) (y j)| ≤ (‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r) :=
      hi.trans (mul_le_mul hx hy (norm_nonneg _) (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg μ)
    simp only [S]
    linarith
  rw [approxSum_filtRes_eq L μ _ J Ψ₁ ψ S (fun j => by linarith [hS1 j]) hsupp]
  exact hL₀ L hL δ hδ n hn z β γ' J S hS1 Ψ₁ hΨ hDer ψ hψ

/-- Real scalars pass through the filtered sum. -/
theorem approxSum_filtRes_smul {n : ℕ} (L μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (ψ : Fin n → ℝ → ℂ) (c : ℝ) :
    approxSum L μ W (filtRes J (fun Ω => c • Ψ₁ Ω) ψ) = c • approxSum L μ W (filtRes J Ψ₁ ψ) := by
  have he : filtRes J (fun Ω => c • Ψ₁ Ω) ψ = fun Ω => c • filtRes J Ψ₁ ψ Ω := by
    funext Ω
    simp only [filtRes, resProfile, Complex.real_smul]
    ring
  rw [he]
  simp only [approxSum, mul_smul_comm]
  exact tsum_const_smul'' c

end WaveTurbulence.Flower.FiltCoh
