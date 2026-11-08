/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT1

/-! # D3 PROT-PIN (P7): auxiliary estimates for root traces of couples

* `tc_rn_oriented`: a couple piece read with its clocks in either order on the full box `timeBox p p`;
* `tc_piece_trace`: a piece at the traced-root clock `s` and the partner clock, on the triangle `triS p p`;
* `tc_jbr_three`, `tc_tsum_T1E`: the exceptional sum of a type-1 root cut keeps the output decay `⟨k⟩^{-N}` at the
  cost `3·6^N` (three outputs `x₁ − x₂ + x₃ = k`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **A couple piece in either clock order**, on the full box. -/
theorem tc_rn_oriented {θ p : ℝ} (f : ℝ → ℝ → ℂ) (c : ℝ → ℝ → Fin 2 → ℝ)
    (hc : (∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) :
    rn θ (timeBox p p) (fun x => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) ≤
      rn θ (timeBox p p) (fun x => f (x 0) (x 1)) := by
  rcases hc with hc | hc
  · exact le_of_eq (rn_congr θ fun x _ => by rw [(hc _ _).1, (hc _ _).2])
  · have hsw := rn_swap θ (timeBox p p) (fun x => f (x 0) (x 1))
    have hpre : ConjCoh.permT swap2 ⁻¹' timeBox p p = timeBox p p := by
      ext x
      simp only [Set.mem_preimage, permT_swap2_apply, timeBox, Set.mem_setOf_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      tauto
    rw [hpre] at hsw
    rw [← hsw]
    exact le_of_eq (rn_congr θ fun x _ => by
      rw [(hc _ _).1, (hc _ _).2, permT_swap2_apply]; rfl)

theorem tc_oriented_cont {f : ℝ → ℝ → ℂ} (c : ℝ → ℝ → Fin 2 → ℝ)
    (hc : (∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u))
    (hf : Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1))) :
    Continuous (fun x : Fin 2 → ℝ => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) := by
  rcases hc with hc | hc
  · simpa only [(hc _ _).1, (hc _ _).2] using hf
  · simp only [(hc _ _).1, (hc _ _).2]
    exact hf.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)

/-- **A piece at the traced clock `s`** (first argument of the orientation) and the partner clock `x 1`. -/
theorem tc_piece_trace {θ : ℝ} (hθ : 0 ≤ θ) {p s : ℝ} (hps : p ≤ s) (hsp : s ≤ p + 1) (f : ℝ → ℝ → ℂ)
    (c : ℝ → ℝ → Fin 2 → ℝ) (hc : (∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u))
    (hf : Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1))) :
    rn θ (triS p p) (fun x => f (c s (x 1) 0) (c s (x 1) 1)) ≤
      Regref.traceConst (r := 2) θ VineEstS3.chiUnit * rn θ (timeBox p p) (fun x => f (x 0) (x 1)) := by
  set h : (Fin 2 → ℝ) → ℂ := fun x => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1) with hh
  have hhc : Continuous h := tc_oriented_cont c hc hf
  have ht := rn_trace hθ (fun _ => p) (B := timeBox p p) (Bt := triS p p) (fun x hx i => by
    fin_cases i
    · exact hx.1.1
    · exact hx.1.2) h hhc 0 s (fun x hx => by
      refine VineEstS3.timeBox_subset_closure_interior p p ⟨?_, ?_⟩
      · simp only [Function.update_self]; exact ⟨hps, hsp⟩
      · rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
        exact hx.1.2)
  have he : (fun x : Fin 2 → ℝ => h (Function.update x 0 s)) = fun x => f (c s (x 1) 0) (c s (x 1) 1) := by
    funext x
    simp [hh]
  rw [he] at ht
  exact ht.trans (mul_le_mul' le_rfl (tc_rn_oriented f c hc))

/-! ### The output decay of a type-1 exceptional sum -/

/-- The decay constant of three outputs. -/
def tcDec (d : ℕ) : ℝ := 3 * 6 ^ (30 * d)

theorem tcDec_nonneg (d : ℕ) : 0 ≤ tcDec d := by unfold tcDec; positivity

theorem tc_jbr_le {d : ℕ} (x₁ x₂ x₃ k : Mom d) (h : x₁ - x₂ + x₃ = k) :
    jbr k ≤ 6 * max (jbr x₁) (max (jbr x₂) (jbr x₃)) := by
  have h1 := Induct.one_le_jbr x₁
  have hn : ∀ x : Mom d, ‖x‖ ≤ jbr x := fun x => by
    unfold jbr
    exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg x])
  have hk : jbr k ≤ 1 + ‖k‖ := by
    unfold jbr
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg k]
  have hnk : ‖k‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ := by
    rw [← h]
    calc ‖x₁ - x₂ + x₃‖ ≤ ‖x₁ - x₂‖ + ‖x₃‖ := norm_add_le _ _
      _ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ := by linarith [norm_sub_le x₁ x₂]
  have hm1 := le_max_left (jbr x₁) (max (jbr x₂) (jbr x₃))
  have hm2 := (le_max_left (jbr x₂) (jbr x₃)).trans (le_max_right (jbr x₁) (max (jbr x₂) (jbr x₃)))
  have hm3 := (le_max_right (jbr x₂) (jbr x₃)).trans (le_max_right (jbr x₁) (max (jbr x₂) (jbr x₃)))
  linarith [hn x₁, hn x₂, hn x₃]

theorem tc_jbr_three {d : ℕ} (x₁ x₂ x₃ k : Mom d) (h : x₁ - x₂ + x₃ = k) (N : ℕ) :
    jbr k ^ N * ((jbr x₁ ^ N)⁻¹ * (jbr x₂ ^ N)⁻¹ * (jbr x₃ ^ N)⁻¹) ≤
      6 ^ N * ((jbr x₂ ^ N)⁻¹ * (jbr x₃ ^ N)⁻¹ + (jbr x₁ ^ N)⁻¹ * (jbr x₃ ^ N)⁻¹ +
        (jbr x₁ ^ N)⁻¹ * (jbr x₂ ^ N)⁻¹) := by
  set a := jbr x₁
  set b := jbr x₂
  set e := jbr x₃
  have ha : 0 < a := jbr_pos x₁
  have hb : 0 < b := jbr_pos x₂
  have he : 0 < e := jbr_pos x₃
  have hk := tc_jbr_le x₁ x₂ x₃ k h
  have hmax : max a (max b e) ^ N ≤ a ^ N + b ^ N + e ^ N := by
    rcases le_total a (max b e) with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total b e with h2 | h2
      · rw [max_eq_right h2]; have := pow_pos ha N; have := pow_pos hb N; linarith
      · rw [max_eq_left h2]; have := pow_pos ha N; have := pow_pos he N; linarith
    · rw [max_eq_left h1]; have := pow_pos hb N; have := pow_pos he N; linarith
  have hkN : jbr k ^ N ≤ 6 ^ N * (a ^ N + b ^ N + e ^ N) := by
    calc jbr k ^ N ≤ (6 * max a (max b e)) ^ N := pow_le_pow_left₀ (jbr_pos k).le hk N
      _ = 6 ^ N * max a (max b e) ^ N := mul_pow _ _ _
      _ ≤ 6 ^ N * (a ^ N + b ^ N + e ^ N) := by gcongr
  have hA := pow_pos ha N
  have hB := pow_pos hb N
  have hE := pow_pos he N
  have hinv : 0 ≤ (a ^ N)⁻¹ * (b ^ N)⁻¹ * (e ^ N)⁻¹ := by positivity
  calc jbr k ^ N * ((a ^ N)⁻¹ * (b ^ N)⁻¹ * (e ^ N)⁻¹)
      ≤ 6 ^ N * (a ^ N + b ^ N + e ^ N) * ((a ^ N)⁻¹ * (b ^ N)⁻¹ * (e ^ N)⁻¹) :=
        mul_le_mul_of_nonneg_right hkN hinv
    _ = 6 ^ N * ((b ^ N)⁻¹ * (e ^ N)⁻¹ + (a ^ N)⁻¹ * (e ^ N)⁻¹ + (a ^ N)⁻¹ * (b ^ N)⁻¹) := by
        field_simp

theorem tc_lp_rel {d : ℕ} (L : ℝ) (a b c : Fin d → ℤ) (h : a - b + c = 0) (k : Mom d) :
    (k + latticePoint L a) - (k + latticePoint L b) + (k + latticePoint L c) = k := by
  have hj : ∀ j, (a j : ℝ) - b j + c j = 0 := fun j => by
    have := congrFun h j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at this
    exact_mod_cast this
  ext j
  simp only [latticePoint, PiLp.add_apply, PiLp.sub_apply]
  have h2 : (a j : ℝ) / L - b j / L + c j / L = 0 := by rw [← sub_div, ← add_div, hj, zero_div]
  linarith

/-- **The exceptional sum of a type-1 root cut** (outputs `k + y_i/L`, `y₁ − y₂ + y₃ = 0`). -/
theorem tc_tsum_T1E {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ENNReal.ofReal (jbr k ^ (30 * d)) * ∑' e : T1E d,
      ENNReal.ofReal (jbr (k + latticePoint L e.1.1) ^ (30 * d))⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L e.1.2.1) ^ (30 * d))⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L e.1.2.2) ^ (30 * d))⁻¹ ≤
      ENNReal.ofReal (tcDec d * (latC d * L ^ d) ^ 2) := by
  set N := 30 * d
  set f : (Fin d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint L y) ^ N)⁻¹ with hf
  have hS := tsum_decay_le hd hL k
  have hp : ∀ x : Mom d, 0 ≤ (jbr x ^ N)⁻¹ := fun x => inv_nonneg.2 (pow_nonneg (jbr_pos x).le _)
  have hpt : ∀ e : T1E d, ENNReal.ofReal (jbr k ^ N) * (f e.1.1 * f e.1.2.1 * f e.1.2.2) ≤
      ENNReal.ofReal (6 ^ N) * (f e.1.2.1 * f e.1.2.2 + f e.1.1 * f e.1.2.2 + f e.1.1 * f e.1.2.1) := by
    rintro ⟨⟨a, b, c⟩, he⟩
    have hr := tc_jbr_three _ _ _ k (tc_lp_rel L a b c he k) N
    simp only [hf]
    have eL : ENNReal.ofReal (jbr k ^ N) * (ENNReal.ofReal (jbr (k + latticePoint L a) ^ N)⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L b) ^ N)⁻¹ * ENNReal.ofReal (jbr (k + latticePoint L c) ^ N)⁻¹) =
        ENNReal.ofReal (jbr k ^ N * ((jbr (k + latticePoint L a) ^ N)⁻¹ * (jbr (k + latticePoint L b) ^ N)⁻¹ *
          (jbr (k + latticePoint L c) ^ N)⁻¹)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg (jbr_pos k).le _), ENNReal.ofReal_mul (mul_nonneg (hp _) (hp _)),
        ENNReal.ofReal_mul (hp _)]
    have eR : ENNReal.ofReal (6 ^ N) * (ENNReal.ofReal (jbr (k + latticePoint L b) ^ N)⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L c) ^ N)⁻¹ + ENNReal.ofReal (jbr (k + latticePoint L a) ^ N)⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L c) ^ N)⁻¹ + ENNReal.ofReal (jbr (k + latticePoint L a) ^ N)⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L b) ^ N)⁻¹) =
        ENNReal.ofReal (6 ^ N * ((jbr (k + latticePoint L b) ^ N)⁻¹ * (jbr (k + latticePoint L c) ^ N)⁻¹ +
          (jbr (k + latticePoint L a) ^ N)⁻¹ * (jbr (k + latticePoint L c) ^ N)⁻¹ +
          (jbr (k + latticePoint L a) ^ N)⁻¹ * (jbr (k + latticePoint L b) ^ N)⁻¹)) := by
      have hq : ∀ x y : Mom d, 0 ≤ (jbr x ^ N)⁻¹ * (jbr y ^ N)⁻¹ := fun x y => mul_nonneg (hp x) (hp y)
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 ^ N),
        ENNReal.ofReal_add (add_nonneg (hq _ _) (hq _ _)) (hq _ _), ENNReal.ofReal_add (hq _ _) (hq _ _),
        ENNReal.ofReal_mul (hp _), ENNReal.ofReal_mul (hp _), ENNReal.ofReal_mul (hp _)]
    show ENNReal.ofReal (jbr k ^ N) * (ENNReal.ofReal (jbr (k + latticePoint L a) ^ N)⁻¹ *
        ENNReal.ofReal (jbr (k + latticePoint L b) ^ N)⁻¹ * ENNReal.ofReal (jbr (k + latticePoint L c) ^ N)⁻¹) ≤ _
    rw [eL]
    refine (ENNReal.ofReal_le_ofReal hr).trans (le_of_eq eR.symm)
  have inj23 : Function.Injective (fun e : T1E d => (e.1.2.1, e.1.2.2)) := by
    rintro ⟨⟨a, b, c⟩, he⟩ ⟨⟨a', b', c'⟩, he'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : a = a' := by
      have := he.trans he'.symm
      linear_combination this
    subst this
    rfl
  have inj13 : Function.Injective (fun e : T1E d => (e.1.1, e.1.2.2)) := by
    rintro ⟨⟨a, b, c⟩, he⟩ ⟨⟨a', b', c'⟩, he'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : b = b' := by
      have := he.trans he'.symm
      linear_combination -this
    subst this
    rfl
  have inj12 : Function.Injective (fun e : T1E d => (e.1.1, e.1.2.1)) := by
    rintro ⟨⟨a, b, c⟩, he⟩ ⟨⟨a', b', c'⟩, he'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : c = c' := by
      have := he.trans he'.symm
      linear_combination this
    subst this
    rfl
  have hpair : ∀ (g : T1E d → (Fin d → ℤ) × (Fin d → ℤ)), Function.Injective g →
      ∑' e, f (g e).1 * f (g e).2 ≤ (∑' y, f y) * ∑' y, f y := by
    intro g hg
    refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hg (fun y : (Fin d → ℤ) × (Fin d → ℤ) => f y.1 * f y.2))
      (le_of_eq ?_)
    rw [show (∑' y : (Fin d → ℤ) × (Fin d → ℤ), f y.1 * f y.2) = ∑' a, ∑' b, f a * f b from
      ENNReal.tsum_prod (f := fun a b => f a * f b), ← ENNReal.tsum_mul_right]
    congr 1
    funext a
    rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_left]
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add]
  have hsq : (∑' y, f y) * ∑' y, f y ≤ ENNReal.ofReal ((latC d * L ^ d) ^ 2) := by
    rw [sq, ENNReal.ofReal_mul (mul_nonneg (latC_nonneg d) (pow_nonneg (by linarith) _))]
    exact mul_le_mul' hS hS
  calc ENNReal.ofReal (6 ^ N) * (∑' e : T1E d, f e.1.2.1 * f e.1.2.2 + ∑' e : T1E d, f e.1.1 * f e.1.2.2 +
        ∑' e : T1E d, f e.1.1 * f e.1.2.1)
      ≤ ENNReal.ofReal (6 ^ N) * (ENNReal.ofReal ((latC d * L ^ d) ^ 2) + ENNReal.ofReal ((latC d * L ^ d) ^ 2) +
          ENNReal.ofReal ((latC d * L ^ d) ^ 2)) := by
        refine mul_le_mul' le_rfl (add_le_add (add_le_add ?_ ?_) ?_)
        · exact (hpair _ inj23).trans hsq
        · exact (hpair _ inj13).trans hsq
        · exact (hpair _ inj12).trans hsq
    _ = ENNReal.ofReal (tcDec d * (latC d * L ^ d) ^ 2) := by
        have h0 : 0 ≤ (latC d * L ^ d) ^ 2 := sq_nonneg _
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold tcDec
        ring

/-! ### The joint output weight (loss-free) -/

/-- The output decay of one output. -/
def tcJ {d : ℕ} (k : Mom d) : ℝ≥0∞ := ENNReal.ofReal (jbr k ^ (30 * d))⁻¹

/-- **The output weight of a root-traced side couple**: the three outputs of a type-1 cut, or one output with two
summed ones. -/
def tcWt {d : ℕ} (L : ℝ) (k : Mom d) : ℝ≥0∞ :=
  (∑' y : T1E d, tcJ (k + latticePoint L y.1.1) * tcJ (k + latticePoint L y.1.2.1) *
      tcJ (k + latticePoint L y.1.2.2)) + tcJ k * ENNReal.ofReal ((latC d * L ^ d) ^ 2)

theorem tc_lp_add {d : ℕ} (L : ℝ) (k : Mom d) (a b : Fin d → ℤ) :
    k + latticePoint L a + latticePoint L b = k + latticePoint L (a + b) := by
  rw [Links.latticePoint_add, add_assoc]

/-- **The summed weight**: `Σ_{y} tcWt(k + y/L) ≤ 2 (latC L^d)³` (the type-1 outputs re-indexed by
`(y, y₁, y₂, y₃) ↦ (y + y₁, y + y₂, y + y₃)`, injective). -/
theorem tc_tsum_tcWt {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ∑' y : Fin d → ℤ, tcWt L (k + latticePoint L y) ≤ ENNReal.ofReal (2 * (latC d * L ^ d) ^ 3) := by
  have hS : ∑' y : Fin d → ℤ, tcJ (k + latticePoint L y) ≤ ENNReal.ofReal (latC d * L ^ d) := tsum_decay_le hd hL k
  have hl0 : 0 ≤ latC d * L ^ d := mul_nonneg (latC_nonneg d) (pow_nonneg (by linarith) _)
  unfold tcWt
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have h1 : ∑' y : Fin d → ℤ, ∑' e : T1E d, tcJ (k + latticePoint L y + latticePoint L e.1.1) *
      tcJ (k + latticePoint L y + latticePoint L e.1.2.1) * tcJ (k + latticePoint L y + latticePoint L e.1.2.2) ≤
      ENNReal.ofReal ((latC d * L ^ d) ^ 3) := by
    rw [← ENNReal.tsum_prod]
    have hinj : Function.Injective (fun q : (Fin d → ℤ) × T1E d =>
        ((q.1 + q.2.1.1, q.1 + q.2.1.2.1), q.1 + q.2.1.2.2)) := by
      rintro ⟨y, ⟨⟨a, b, c⟩, he⟩⟩ ⟨y', ⟨⟨a', b', c'⟩, he'⟩⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hy : y = y' := by
        have e1 : y = (y + a) - (y + b) + (y + c) := by linear_combination -he
        have e2 : y' = (y' + a') - (y' + b') + (y' + c') := by linear_combination -he'
        rw [e1, e2, h1, h2, h3]
      subst hy
      have ha : a = a' := by simpa using h1
      have hb : b = b' := by simpa using h2
      have hc : c = c' := by simpa using h3
      subst ha hb hc
      rfl
    refine le_trans (le_of_eq ?_) ((ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun z : ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin d → ℤ) =>
        tcJ (k + latticePoint L z.1.1) * tcJ (k + latticePoint L z.1.2) * tcJ (k + latticePoint L z.2))).trans ?_)
    · refine tsum_congr fun q => ?_
      simp only [tc_lp_add]
    · set F : (Fin d → ℤ) → ℝ≥0∞ := fun a => tcJ (k + latticePoint L a) with hF
      have e3 : ∑' z : ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin d → ℤ), F z.1.1 * F z.1.2 * F z.2 =
          (∑' a, F a) * (∑' b, F b) * ∑' c, F c := by
        rw [ENNReal.tsum_prod (f := fun (ab : (Fin d → ℤ) × (Fin d → ℤ)) c => F ab.1 * F ab.2 * F c)]
        simp only [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun a b => F a * F b)]
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      show ∑' z : ((Fin d → ℤ) × (Fin d → ℤ)) × (Fin d → ℤ), F z.1.1 * F z.1.2 * F z.2 ≤ _
      rw [e3]
      calc (∑' a, F a) * (∑' b, F b) * ∑' c, F c
          ≤ ENNReal.ofReal (latC d * L ^ d) * ENNReal.ofReal (latC d * L ^ d) * ENNReal.ofReal (latC d * L ^ d) :=
            mul_le_mul' (mul_le_mul' hS hS) hS
        _ = ENNReal.ofReal ((latC d * L ^ d) ^ 3) := by
            rw [← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul (mul_nonneg hl0 hl0)]
            congr 1; ring
  have h1' : ∑' y : Fin d → ℤ, ∑' e : T1E d, tcJ (k + latticePoint L y + latticePoint L e.1.1) *
      tcJ (k + latticePoint L y + latticePoint L e.1.2.1) * tcJ (k + latticePoint L y + latticePoint L e.1.2.2) =
      ∑' y : Fin d → ℤ, ∑' e : T1E d, tcJ (k + latticePoint L y + latticePoint L e.1.1) *
      tcJ (k + latticePoint L y + latticePoint L e.1.2.1) * tcJ (k + latticePoint L y + latticePoint L e.1.2.2) := rfl
  calc (∑' y : Fin d → ℤ, ∑' e : T1E d, tcJ (k + latticePoint L y + latticePoint L e.1.1) *
          tcJ (k + latticePoint L y + latticePoint L e.1.2.1) * tcJ (k + latticePoint L y + latticePoint L e.1.2.2)) +
        (∑' y : Fin d → ℤ, tcJ (k + latticePoint L y)) * ENNReal.ofReal ((latC d * L ^ d) ^ 2)
      ≤ ENNReal.ofReal ((latC d * L ^ d) ^ 3) + ENNReal.ofReal (latC d * L ^ d) * ENNReal.ofReal ((latC d * L ^ d) ^ 2) :=
        add_le_add h1 (mul_le_mul' hS le_rfl)
    _ = ENNReal.ofReal (2 * (latC d * L ^ d) ^ 3) := by
        rw [← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- Sums over the exceptional pairs of a chain pair, two different weights. -/
theorem tc_tsum_pairE_le2 {d : ℕ} (m : MiniTreeCode) (f g : (Fin d → ℤ) → ℝ≥0∞) :
    ∑' e : PairE m d, f e.1.2.1 * g e.1.2.2 ≤ (∑' y, f y) * ∑' y, g y := by
  have hinj : Function.Injective (fun e : PairE m d => (e.1.2.1, e.1.2.2)) := by
    intro e e' h
    simp only [Prod.mk.injEq] at h
    have hx : e.1.1 = e'.1.1 := by rw [e.2.2, e'.2.2, h.1, h.2]
    exact Subtype.ext (Prod.ext hx (Prod.ext h.1 h.2))
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun y : (Fin d → ℤ) × (Fin d → ℤ) => f y.1 * g y.2))
    (le_of_eq ?_)
  rw [show (∑' y : (Fin d → ℤ) × (Fin d → ℤ), f y.1 * g y.2) = ∑' a, ∑' b, f a * g b from
    ENNReal.tsum_prod (f := fun a b => f a * g b), ← ENNReal.tsum_mul_right]
  congr 1
  funext a
  rw [ENNReal.tsum_mul_left]

theorem tc_tcWt_lt_top {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) : tcWt L k < ⊤ := by
  unfold tcWt
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  have h := tc_tsum_T1E hd hL k
  have hpos : ENNReal.ofReal (jbr k ^ (30 * d)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos (jbr_pos k) _
  have hlt : ENNReal.ofReal (jbr k ^ (30 * d)) * (∑' y : T1E d, tcJ (k + latticePoint L y.1.1) *
      tcJ (k + latticePoint L y.1.2.1) * tcJ (k + latticePoint L y.1.2.2)) < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne hpos

end WaveTurbulence.Flower.ProtPin
