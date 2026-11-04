/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI5

/-!
# DH21 Lemma 5.7: the three class `R` pieces

`exists_piece_IRIR` converts a coupling `K(x₀, x₁, q)` of the forms `LsIRIR` with a `Γ` bound into a
parametric basic class `R` operator with special variable `α₁` on the variables
`(ι ⊕ Empty) ⊕ Unit` (`α₂ = α (inr ())`), via `lintegral_tripleS_le` with the special variable `α₂`
and `RSymP.ofAnyE` (third coefficient `γ₁`). The three pieces are DH21 terms V and VI.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Generic

/-- The weighted norm of a class `R` piece of `I_{εα₁} ℛ I_{μ₁-εα₁}`. -/
theorem lintegral_piece_IRIR_le {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]
    {θ A N : ℝ} (h0 : 0 ≤ θ) (hA : 0 ≤ A) {R : RSym ι} (hR : R.Bound θ A N)
    {K : (Fin 2 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) {c : (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 2 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 2 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ α z, wR θ α (c z).1 z.1.1 ≤ (Cw : ℝ≥0∞) * wR θ (vA α) z.1.1 z.1.2.2 +
      wc (formsV (LsIRIR R) (csIRIR Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      wc (formsV (LsIRIR R) (csIRIR Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRIR R) (csIRIR Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wR θ α (c z).1 z.1.1 *
      dnorm k (tripleS R.m oneSym K (LsIRIR R) (csIRIR Q)) α z ≤
        gev (3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) A k := by
  have hN := hR.nonneg
  have hCw' : (1 : ℝ) ≤ Cw := by exact_mod_cast hCw
  set w₁ : Fin 3 → (ι → ℝ) → ℝ × ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => (Cw : ℝ≥0∞) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (Empty → ℝ) → Unit → ℝ≥0∞ := fun _ _ _ => 1 with hw₂d
  set w₃ : Fin 3 → (Unit → ℝ) → (Fin 2 → ℝ) → Q → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ x q => wc x q, fun _ _ _ => 0] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
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
  have hW' : ∀ α z, wR θ α (c z).1 z.1.1 ≤ ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
      w₃ p (vS α) (formsV (LsIRIR R) (csIRIR Q) α z) z.2.2 := fun α z => by
    subst hw₁d hw₂d hw₃d
    simp only [Fin.sum_univ_three, Matrix.cons_val, mul_one, one_mul, mul_zero, add_zero]
    exact hW α z
  have hΓ' : ∀ p k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ) (z₂ : Unit), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w₃ p s (formsV (LsIRIR R) (csIRIR Q) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRIR R) (csIRIR Q) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤ gev NK A k := by
    intro p k a z₁ z₂
    obtain ⟨⟩ := z₂
    subst hw₃d; fin_cases p
    · refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) (hΓ k a z₁)
      exact mul_le_mul' (hone _ _) le_rfl
    · exact hΓ k a z₁
    · simp
  have key := lintegral_tripleS_le (m₁ := R.m) (m₂ := oneSym) (K := K) (Ls := LsIRIR R)
    (cs := csIRIR Q) (isBundle_LsIRIR hR) hR.reg symReg_oneSym hK hKm (measurable_csIRIR Q)
    (fun α z => wR θ α (c z).1 z.1.1) w₁ w₂ w₃ hw₁ hw₂ hw₃ hW' (fun _ k => gev NK A k) hΓ' k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j oneSym b z₂)
    (S₃ := fun _ j => gev NK A j) (by positivity) zero_le_one hNK hA
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact (RS_bounds h0 hR j Cw).2
    · exact (RS_bounds h0 hR j Cw).1.trans (gev_le_mul hN hA hCw' j)
    · exact (RS_bounds h0 hR j Cw).1.trans (gev_le_mul hN hA hCw' j)
  · subst hw₂d; exact lintegral_oneSym_le A j

/-- **A class `R` piece of `I_{εα₁} ℛ I_{μ₁-εα₁}`**, parametric in `(p, μ₁)`; denominator
`ℓ₂ + ε₂α₂ + εα₁ + γ₁`. -/
theorem exists_piece_IRIR {P : Type*} [MeasurableSpace P] {Q : Type*} [MeasureSpace Q]
    [SFinite (volume : Measure Q)] {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : 0 ≤ A)
    {R : RSymP P ι} (hR : R.Bound θ A N) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {y₂ : (ι ⊕ Empty) ⊕ Unit → ℤ} (hy₂ : IsBundle y₂)
    {K : (Fin 2 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedFDeriv ℝ k (fun x => K x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) {c : ℝ → (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    (hc : Measurable fun x : ℝ × ((ℝ × ℝ × ℝ) × (Unit × Q)) => c x.1 x.2)
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 2 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 2 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ (p : P) μ α z, wR θ α (c μ z).1 z.1.1 ≤ (Cw : ℝ≥0∞) * wR θ (vA α) z.1.1 z.1.2.2 +
      wc (formsV (LsIRIR (R.get p)) (csIRIR Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ (p : P) k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      wc (formsV (LsIRIR (R.get p)) (csIRIR Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRIR (R.get p)) (csIRIR Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) :
    ∃ S : RSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * (Cw * N) * 1 * NK))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z, tripleS (R.get p.1).m oneSym K (LsIRIR (R.get p.1)) (csIRIR Q) (nsp α) z *
          rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
            (bundle y₂ (nsp α) + ε * α none) (c p.2 z).1 (c p.2 z).2 z.1.1 t s := by
  have hN := hR.nonneg
  have hNt : 0 ≤ 3 * (16 * ((Cw : ℝ) * N) * 1 * NK) := by positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R.get p).m)
    (m₂ := fun (_ : ℝ) => oneSym) hR.meas stronglyMeasurable_const hKm
    ![y3 (fun i => -R.y₂ i) 0 (-R.ε), y3 R.y₁ 0 R.ε] (measurable_csIRIR Q)
  obtain ⟨S, -, -, -, hS, hk⟩ := RSymP.ofAnyE (P := P × ℝ) (θ := θ) (A := A)
    (N := 3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) hε
    (isBundle_y3 hR.bundle₂ isBundle_zero (abs_sign_le hR.sign)) hy₂
    (a := fun p => tripleS (R.get p.1).m oneSym K (LsIRIR (R.get p.1)) (csIRIR Q))
    (fun p => tripleS_symReg (isBundle_LsIRIR (hR.bound p.1)) (hR.bound p.1).reg
      symReg_oneSym hK hKm (measurable_csIRIR Q) G hGm hG hGi) hm
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ × ℝ) (γ := Unit × Q))
    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ × ℝ) (γ₁ := Unit × Q))
    (c := fun p z => c p.2 z)
    (hc.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) h0 h1 hNt
    (fun p k => lintegral_piece_IRIR_le h0 hA (hR.bound p.1) hK hKm hCw hwc
      hone (hW p.1 p.2) hNK (hΓ p.1) k)
  exact ⟨S, hS, hk⟩

end Generic

section Pieces

variable {θ A N : ℝ} {P : Type*} [MeasurableSpace P] {R : RSymP P ι} {ε : ℤ}

/-- **DH21 term V for Lemma 5.7** (phase `ℓ₂ + ε₂α₂ + εα₁`, `γ' = (γ₁ + σ, γ₂ + μ - σ, γ₁)`). -/
theorem exists_piece_IRIR_ba (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((4 : ℕ) * N) * 1 * (16 * (CkM * IM) * CPhi)))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS (R.get p.1).m oneSym KRV (LsIRIR (R.get p.1)) (csIRIR _) (nsp α) z *
            rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
              (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
              (z.1.1 + z.2.2.1) (z.1.2.1 + p.2 - z.2.2.1) z.1.1 t s := by
  have hNK : 0 ≤ 16 * (CkM * IM) * CPhi := by
    have := mul_nonneg kerM_bound.1 IM_nonneg; have := CPhi_nonneg; positivity
  exact exists_piece_IRIR h0 h1.le (A0_nonneg.trans hA) hR hε
    (isBundle_y3 hR.bundle₂ isBundle_zero (abs_sign_le hR.sign)) contDiff_KRV
    measurable_KRV.stronglyMeasurable GMR measurable_GMR enorm_KRV_le_G lintegral_GMR_ne_top
    (c := fun μ z => (z.1.1 + z.2.2.1, z.1.2.1 + μ - z.2.2.1)) (by fun_prop) (Cw := 4)
    (by norm_num) (wc := fun x q => (1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)) (by fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun _ _ α z => by
      simp only [formsV_IRIR_one, Nat.cast_ofNat]
      exact split_IRIR_ba h0 h1.le hR.sign hR.bundle₁ α z.1.1 z.1.2.2 z.2.2.1)
    hNK
    (fun _ k a z₁ => gamma_KRV_le (sign_neg hR.sign)
      (z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i))) _
      (fun s q => by
        rw [formsV_IRIR_zero]
        show z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i)) - (R.ε : ℝ) * s () = _
        push_cast; ring)
      k hA)

/-- **DH21 term VI, first part, for Lemma 5.7** (phase `εα₁`, `γ' = (γ₁ + γ₂, μ, γ₁)`). -/
theorem exists_piece_IRIR_bb (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * (16 * Cθ θ * (CPhi * CPhi))))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
          tripleS (R.get p.1).m oneSym KRVI (LsIRIR (R.get p.1)) (csIRIR _) (nsp α) z *
            rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
              (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (nsp α) + ε * α none)
              (z.1.1 + z.1.2.1) p.2 z.1.1 t s := by
  have hNK : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  exact exists_piece_IRIR h0 h1.le (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_KRVI
    measurable_KRVI.stronglyMeasurable GPR (fun _ => measurable_const) enorm_KRVI_le_G
    lintegral_GPR_ne_top
    (c := fun μ z => (z.1.1 + z.1.2.1, μ)) (by fun_prop) (Cw := 7)
    (by norm_num) (wc := fun x _ => (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1) (by fun_prop)
    (fun x q => le_add_left le_rfl)
    (fun _ _ α z => by
      simp only [formsV_IRIR_zero, formsV_IRIR_one, Nat.cast_ofNat]
      exact split_IRIR_bb h0 h1.le hR.sign hR.bundle₁ hR.bundle₂ α z.1.1 z.1.2.1 z.1.2.2)
    hNK
    (fun _ k a z₁ => gamma_KRVI_le h0 h1 (sign_neg hR.sign) hR.sign
      (z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i)))
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by
        rw [formsV_IRIR_zero]
        show z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i)) - (R.ε : ℝ) * s () = _
        push_cast; ring)
      (fun s q => by rw [formsV_IRIR_one]; rfl) k hA)

/-- **DH21 term VI, second part, for Lemma 5.7** (phase `ℓ₂ + ε₂α₂ + εα₁`,
`γ' = (γ₁, γ₂ + μ, γ₁)`). -/
theorem exists_piece_IRIR_bc (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * (16 * Cθ θ * (CPhi * CPhi))))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
          tripleS (R.get p.1).m oneSym KRVI (LsIRIR (R.get p.1)) (csIRIR _) (nsp α) z *
            rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
              (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp α) + ε * α none)
              z.1.1 (z.1.2.1 + p.2) z.1.1 t s := by
  have hNK : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  exact exists_piece_IRIR h0 h1.le (A0_nonneg.trans hA) hR hε
    (isBundle_y3 hR.bundle₂ isBundle_zero (abs_sign_le hR.sign)) contDiff_KRVI
    measurable_KRVI.stronglyMeasurable GPR (fun _ => measurable_const) enorm_KRVI_le_G
    lintegral_GPR_ne_top
    (c := fun μ z => (z.1.1, z.1.2.1 + μ)) (by fun_prop) (Cw := 7)
    (by norm_num) (wc := fun x _ => (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1) (by fun_prop)
    (fun x q => le_add_left le_rfl)
    (fun _ _ α z => by
      simp only [formsV_IRIR_zero, formsV_IRIR_one, Nat.cast_ofNat]
      exact split_IRIR_bc h0 h1.le hR.sign hR.bundle₁ α z.1.1 z.1.2.1 z.1.2.2)
    hNK
    (fun _ k a z₁ => gamma_KRVI_le h0 h1 (sign_neg hR.sign) hR.sign
      (z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i)))
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by
        rw [formsV_IRIR_zero]
        show z₁.2.1 - bundle R.y₂ (fun i => a (Sum.inl i)) - (R.ε : ℝ) * s () = _
        push_cast; ring)
      (fun s q => by rw [formsV_IRIR_one]; rfl) k hA)

end Pieces

end WaveTurbulence.ClassJR
