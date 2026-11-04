/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI2
public import WaveTurbulence.Foundations.ClassJR.ParamJR

/-!
# DH21 Lemma 5.6: the six class `J` pieces

`exists_piece_IJI` turns a coupling `K` of the two forms `y`, `x` with a `Γ` bound and a
weight split into a basic class `J` operator (via `lintegral_tripleS_le` with the trivial second
symbol and `JSymP.ofAny`); it is applied to the couplings of DH21 terms I–IV. The input operator is
parametric in `p ∈ P` and the output is parametric in `(p, μ₁) ∈ P × ℝ`; the coefficient map
depends on `μ₁` only (`lintegral_piece_IJI_le` is the bound for one member).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Generic

theorem lintegral_wJ_dnorm_le {θ A N : ℝ} {R : JSym ι} (h : R.Bound θ A N) (c : ℕ) (j : ℕ) :
    ∫⁻ a, ∫⁻ γ : ℝ × ℝ, (c : ℝ≥0∞) * wJ θ a γ.1 * dnorm j R.m a γ ≤ gev (c * N) A j := by
  have : ∫⁻ a, ∫⁻ γ : ℝ × ℝ, (c : ℝ≥0∞) * wJ θ a γ.1 * dnorm j R.m a γ =
      (c : ℝ≥0∞) * jNorm θ j R.m := by
    unfold jNorm
    simp_rw [mul_assoc]
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_congr fun b => ?_
    rw [lintegral_const_mul' _ _ (by simp)]
  rw [this, show (c : ℝ≥0∞) = ENNReal.ofReal c by simp]
  exact (mul_le_mul' le_rfl (h.norm j)).trans_eq (gev_mul_const _ (by positivity) j)

theorem lintegral_oneSym_le (A : ℝ) (j : ℕ) :
    ∫⁻ b : Empty → ℝ, ∫⁻ z : Unit, (fun _ _ => (1 : ℝ≥0∞)) b z * dnorm j oneSym b z ≤
      gev 1 A j := by
  rw [lintegral_emptyFun, lintegral_unit, one_mul]
  refine (dnorm_const_le j (fun _ => (1 : ℂ)) _ _).trans ?_
  split_ifs with hj
  · subst hj; simp [gev]
  · simp

/-- The weighted norm of a class `J` piece of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`. -/
theorem lintegral_piece_IJI_le {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]
    {θ A N : ℝ} (h0 : 0 ≤ θ) (hA : 0 ≤ A) {R : JSym ι} (hR : R.Bound θ A N)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {K : (Fin 2 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) {c : (ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 2 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 2 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ α z, wJ θ α (c z).1 ≤ (Cw : ℝ≥0∞) * wJ θ (vA α) z.1.1 +
      wc (formsV (LsIJI R ε) (csIJI Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      wc (formsV (LsIJI R ε) (csIJI Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIJI R ε) (csIJI Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α (c z).1 * dnorm k (tripleS R.m oneSym K (LsIJI R ε) (csIJI Q)) α z ≤
      gev (3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) A k := by
  have hN := hR.nonneg
  have hCw' : (1 : ℝ) ≤ Cw := by exact_mod_cast hCw
  set w₁ : Fin 3 → (ι → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => (Cw : ℝ≥0∞) * wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (Empty → ℝ) → Unit → ℝ≥0∞ := fun _ _ _ => 1 with hw₂d
  set w₃ : Fin 3 → (Unit → ℝ) → (Fin 2 → ℝ) → Q → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ x q => wc x q, fun _ _ _ => 0] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wJ θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; exact measurable_const
  have hw₃ : ∀ p, Measurable fun t : (Unit → ℝ) × ((Fin 2 → ℝ) × Q) =>
      w₃ p t.1 t.2.1 t.2.2 := by
    intro p; subst hw₃d; fin_cases p
    · exact measurable_const
    · exact hwc.comp measurable_snd
    · exact measurable_const
  have hW' : ∀ α z, wJ θ α (c z).1 ≤ ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
      w₃ p (vS α) (formsV (LsIJI R ε) (csIJI Q) α z) z.2.2 := fun α z => by
    subst hw₁d hw₂d hw₃d
    simp only [Fin.sum_univ_three, Matrix.cons_val, mul_one, one_mul, mul_zero, add_zero]
    exact hW α z
  have hΓ' : ∀ p k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ) (z₂ : Unit), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w₃ p s (formsV (LsIJI R ε) (csIJI Q) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIJI R ε) (csIJI Q) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤ gev NK A k := by
    intro p k a z₁ z₂
    obtain ⟨⟩ := z₂
    subst hw₃d; fin_cases p
    · refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) (hΓ k a z₁)
      exact mul_le_mul' (hone _ _) le_rfl
    · exact hΓ k a z₁
    · simp
  have key := lintegral_tripleS_le (m₁ := R.m) (m₂ := oneSym) (K := K) (Ls := LsIJI R ε)
    (cs := csIJI Q) (isBundle_LsIJI hR hε) hR.reg symReg_oneSym hK hKm (measurable_csIJI Q)
    (fun α z => wJ θ α (c z).1) w₁ w₂ w₃ hw₁ hw₂ hw₃ hW' (fun _ k => gev NK A k) hΓ' k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j oneSym b z₂)
    (S₃ := fun _ j => gev NK A j) (by positivity) zero_le_one hNK hA
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact lintegral_wJ_dnorm_le hR Cw j
    · exact (S_bounds h0 hR j).2.1.trans (gev_le_mul hN hA hCw' j)
    · exact (S_bounds h0 hR j).2.1.trans (gev_le_mul hN hA hCw' j)
  · subst hw₂d; exact lintegral_oneSym_le A j

/-- **A class `J` piece of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`**, parametric in `(p, μ₁)`. -/
theorem exists_piece_IJI {P : Type*} [MeasurableSpace P] {Q : Type*} [MeasureSpace Q]
    [SFinite (volume : Measure Q)] {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : 0 ≤ A)
    {R : JSymP P ι} (hR : R.Bound θ A N) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {y : (ι ⊕ Empty) ⊕ Unit → ℤ} (hy : IsBundle y)
    {K : (Fin 2 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedFDeriv ℝ k (fun x => K x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) {c : ℝ → (ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    (hc : Measurable fun x : ℝ × ((ℝ × ℝ) × (Unit × Q)) => c x.1 x.2)
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 2 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 2 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ (p : P) μ α z, wJ θ α (c μ z).1 ≤ (Cw : ℝ≥0∞) * wJ θ (vA α) z.1.1 +
      wc (formsV (LsIJI (R.get p) ε) (csIJI Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ (p : P) k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      wc (formsV (LsIJI (R.get p) ε) (csIJI Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIJI (R.get p) ε) (csIJI Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * (Cw * N) * 1 * NK))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z, tripleS (R.get p.1).m oneSym K (LsIJI (R.get p.1) ε) (csIJI Q) α z *
          jker (bundle y α) (c p.2 z).1 (c p.2 z).2 t s := by
  have hN := hR.nonneg
  have hNt : 0 ≤ 3 * (16 * ((Cw : ℝ) * N) * 1 * NK) := by positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R.get p).m)
    (m₂ := fun (_ : ℝ) => oneSym) hR.meas stronglyMeasurable_const hKm
    ![y3 R.y 0 ε, y3 0 0 ε] (measurable_csIJI Q)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofAny (P := P × ℝ) (θ := θ) (A := A)
    (N := 3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) hy
    (a := fun p => tripleS (R.get p.1).m oneSym K (LsIJI (R.get p.1) ε) (csIJI Q))
    (fun p => tripleS_symReg (isBundle_LsIJI (hR.bound p.1) hε) (hR.bound p.1).reg
      symReg_oneSym hK hKm (measurable_csIJI Q) G hGm hG hGi) hm
    (c := fun p z => c p.2 z)
    (hc.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) h0 h1 hNt
    (fun p k => lintegral_piece_IJI_le h0 hA (hR.bound p.1) hε hK hKm hCw hwc
      hone (hW p.1 p.2) hNK (hΓ p.1) k)
  exact ⟨S, hS, hk⟩

end Generic

end WaveTurbulence.ClassJR
