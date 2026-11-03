/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ParamComp

/-!
# DH21 Lemmas 5.4–5.5 with parameters: the pieces

Joint measurability of the product symbols with special variables
(`stronglyMeasurable_tripleS_param`), relabelling of parametric class `J` operators
(`ClassJP.reindex`), and the nine parametric basic pieces of `J R`, `R J`, `R R`. The forms
`LsJR`, `LsRJ`, `LsRR` only involve the bundles and signs, which are common to a parametric family,
so the pieces are obtained from the non-parametric ones by `JSymP.ofGenE`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Measurability

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {κ₁ κ₂ σ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype σ]
variable {Γ₁ Γ₂ Q : Type*} [MeasurableSpace Γ₁] [MeasurableSpace Γ₂] [MeasurableSpace Q]

theorem stronglyMeasurable_tripleS_param {m₁ : P₁ → (κ₁ → ℝ) → Γ₁ → ℂ}
    {m₂ : P₂ → (κ₂ → ℝ) → Γ₂ → ℂ}
    (h₁ : StronglyMeasurable fun x : P₁ × ((κ₁ → ℝ) × Γ₁) => m₁ x.1 x.2.1 x.2.2)
    (h₂ : StronglyMeasurable fun x : P₂ × ((κ₂ → ℝ) × Γ₂) => m₂ x.1 x.2.1 x.2.2)
    {n : ℕ} {K : (Fin n → ℝ) → Q → ℂ} (hK : StronglyMeasurable (Function.uncurry K))
    (Ls : Fin n → (κ₁ ⊕ κ₂) ⊕ σ → ℤ) {cs : Fin n → Γ₁ × (Γ₂ × Q) → ℝ}
    (hc : ∀ r, Measurable (cs r)) :
    StronglyMeasurable fun x : (P₁ × P₂) × (((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (Γ₁ × (Γ₂ × Q))) =>
      tripleS (m₁ x.1.1) (m₂ x.1.2) K Ls cs x.2.1 x.2.2 := by
  have hα : Measurable fun x : (P₁ × P₂) × (((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (Γ₁ × (Γ₂ × Q))) => x.2.1 :=
    measurable_fst.comp measurable_snd
  have hz : Measurable fun x : (P₁ × P₂) × (((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (Γ₁ × (Γ₂ × Q))) => x.2.2 :=
    measurable_snd.comp measurable_snd
  unfold tripleS
  exact ((h₁.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_vA.comp hα).prodMk (measurable_fst.comp hz)))).mul
    (h₂.comp_measurable ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_vB.comp hα).prodMk (measurable_fst.comp (measurable_snd.comp hz)))))).mul
    (hK.comp_measurable (((measurable_formsV (Ls := Ls) hc).comp (hα.prodMk hz)).prodMk
      (measurable_snd.comp (measurable_snd.comp hz))))

end Measurability

section Reindex

variable {P : Type*} [MeasurableSpace P] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The relabelled parametric basic class `J` datum. -/
@[expose] def JSymP.reindex (e : ι ≃ ι') (R : JSymP P ι) : JSymP P ι' where
  y := fun j => R.y (e.symm j)
  m := fun p α' γ => R.m p (fun i => α' (e i)) γ

theorem JSymP.Bound.reindex (e : ι ≃ ι') {R : JSymP P ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    (R.reindex e).Bound θ A N where
  bound p := (h.bound p).reindex e
  meas := by
    have hmap : Measurable fun x : P × ((ι' → ℝ) × (ℝ × ℝ)) =>
        ((x.1, ((fun i => x.2.1 (e i)), x.2.2)) : P × ((ι → ℝ) × (ℝ × ℝ))) :=
      measurable_fst.prodMk ((Measurable.of_eval fun i => (measurable_pi_apply (e i)).comp
        (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
    exact h.meas.comp_measurable hmap
  nonneg := h.nonneg
  bundle j := h.bundle (e.symm j)

/-- **Relabelling the variables of a parametric class `J` operator.** -/
theorem ClassJP.reindex (e : ι ≃ ι') {θ A N : ℝ} {T : P → (ι → ℝ) → ℝ → ℝ → ℂ}
    (h : ClassJP θ A N T) : ClassJP θ A N fun p α' => T p fun i => α' (e i) := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  refine ⟨n, fun i => (R i).reindex e, c, fun i => (hb i).reindex e, hs, fun p α' => ?_⟩
  intro t s h0 h1 h2
  beta_reduce
  rw [he _ _ t s h0 h1 h2]
  exact Finset.sum_congr rfl fun i _ => (JSym.reindex_kernel e ((R i).get p) α' t s).symm

end Reindex

section PiecesJR

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {θ A N₁ N₂ : ℝ} {R₁ : JSymP P₁ ι₁} {R₂ : RSymP P₂ ι₂}

theorem exists_pieceP_JR_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KMR (LsJR (R₁.get p.1) (R₂.get p.2)) (csJR (ℝ × ℝ)) α z *
          jker (bundle (yJRL (ι₂ := ι₂) (R₁.get p.1)) α) ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1)
            ((eJR (ℝ × ℝ) z).1.2 + (bMR (eJR (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi)) := by have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KMR.stronglyMeasurable
    ![y3 (fun i => -R₁.y i) R₂.y₂ R₂.ε, y3 0 R₂.y₁ R₂.ε] (measurable_csJR (ℝ × ℝ))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (g := (0 : ι₂ → ℤ)) h₁.bundle isBundle_zero (show |(0 : ℤ)| ≤ 1 by simp))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KMR (LsJR (R₁.get p.1) (R₂.get p.2))
      (csJR (ℝ × ℝ)))
    (fun p => symReg_piece_JR_M (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJR (ℝ × ℝ)) (measurePreserving_eJR _) measurable_bMR hC
    (fun p => norm_piece_JR_M h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_JR_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPR (LsJR (R₁.get p.1) (R₂.get p.2)) (csJR Unit) α z *
          jker (bundle (yJRR (ι₁ := ι₁) (R₂.get p.2)) α) ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1)
            ((eJR Unit z).1.2 + (bP1R (eJR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi))) := by have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPR.stronglyMeasurable
    ![y3 (fun i => -R₁.y i) R₂.y₂ R₂.ε, y3 0 R₂.y₁ R₂.ε] (measurable_csJR Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (f := (0 : ι₁ → ℤ)) isBundle_zero h₂.bundle₂ (abs_sign_le h₂.sign))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPR (LsJR (R₁.get p.1) (R₂.get p.2))
      (csJR Unit))
    (fun p => symReg_piece_JR_P1 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJR Unit) (measurePreserving_eJR _) measurable_bP1R hC
    (fun p => norm_piece_JR_P1 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_JR_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPRn (LsJR (R₁.get p.1) (R₂.get p.2)) (csJR Unit) α z *
          jker (bundle (yJRL (ι₂ := ι₂) (R₁.get p.1)) α) ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1)
            ((eJR Unit z).1.2 + (bP2R (eJR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi))) := by have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPRn.stronglyMeasurable
    ![y3 (fun i => -R₁.y i) R₂.y₂ R₂.ε, y3 0 R₂.y₁ R₂.ε] (measurable_csJR Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (g := (0 : ι₂ → ℤ)) h₁.bundle isBundle_zero (show |(0 : ℤ)| ≤ 1 by simp))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPRn (LsJR (R₁.get p.1) (R₂.get p.2))
      (csJR Unit))
    (fun p => symReg_piece_JR_P2 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJR Unit) (measurePreserving_eJR _) measurable_bP2R hC
    (fun p => norm_piece_JR_P2 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

end PiecesJR

section PiecesRJ

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {θ A N₁ N₂ : ℝ} {R₁ : RSymP P₁ ι₁} {R₂ : JSymP P₂ ι₂}

theorem exists_pieceP_RJ_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KMR (LsRJ (R₁.get p.1) (R₂.get p.2)) (csRJ (ℝ × ℝ)) α z *
          jker (bundle (yRJL (ι₂ := ι₂) (R₁.get p.1)) α) ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1)
            ((eRJ (ℝ × ℝ) z).1.2 + (bMR (eRJ (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi)) := by have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KMR.stronglyMeasurable
    ![y3 (fun i => -R₁.y₂ i) R₂.y (-R₁.ε), y3 R₁.y₁ 0 R₁.ε] (measurable_csRJ (ℝ × ℝ))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (g := (0 : ι₂ → ℤ)) h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KMR (LsRJ (R₁.get p.1) (R₂.get p.2))
      (csRJ (ℝ × ℝ)))
    (fun p => symReg_piece_RJ_M (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRJ (ℝ × ℝ)) (measurePreserving_eRJ _) measurable_bMR hC
    (fun p => norm_piece_RJ_M h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_RJ_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPR (LsRJ (R₁.get p.1) (R₂.get p.2)) (csRJ Unit) α z *
          jker (bundle (yRJR (ι₁ := ι₁) (R₂.get p.2)) α) ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1)
            ((eRJ Unit z).1.2 + (bP1R (eRJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi))) := by have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPR.stronglyMeasurable
    ![y3 (fun i => -R₁.y₂ i) R₂.y (-R₁.ε), y3 R₁.y₁ 0 R₁.ε] (measurable_csRJ Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (f := (0 : ι₁ → ℤ)) isBundle_zero h₂.bundle (show |(0 : ℤ)| ≤ 1 by simp))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPR (LsRJ (R₁.get p.1) (R₂.get p.2))
      (csRJ Unit))
    (fun p => symReg_piece_RJ_P1 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRJ Unit) (measurePreserving_eRJ _) measurable_bP1R hC
    (fun p => norm_piece_RJ_P1 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_RJ_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit), S.Bound θ A (3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi)))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPRn (LsRJ (R₁.get p.1) (R₂.get p.2)) (csRJ Unit) α z *
          jker (bundle (yRJL (ι₂ := ι₂) (R₁.get p.1)) α) ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1)
            ((eRJ Unit z).1.2 + (bP2R (eRJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi))) := by have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPRn.stronglyMeasurable
    ![y3 (fun i => -R₁.y₂ i) R₂.y (-R₁.ε), y3 R₁.y₁ 0 R₁.ε] (measurable_csRJ Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y3 (g := (0 : ι₂ → ℤ)) h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPRn (LsRJ (R₁.get p.1) (R₂.get p.2))
      (csRJ Unit))
    (fun p => symReg_piece_RJ_P2 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRJ Unit) (measurePreserving_eRJ _) measurable_bP2R hC
    (fun p => norm_piece_RJ_P2 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

end PiecesRJ

section PiecesRR

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {θ A N₁ N₂ : ℝ} {R₁ : RSymP P₁ ι₁} {R₂ : RSymP P₂ ι₂}

theorem exists_pieceP_RR_M (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Fin 2), S.Bound θ A (3 * (16 * (3 * N₁) * (3 * N₂) * NMRR θ)) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KMRR (LsRR (R₁.get p.1) (R₂.get p.2)) (csRR (ℝ × ℝ)) α z *
          jker (bundle (yRRL (ι₂ := ι₂) (R₁.get p.1)) α) ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1)
            ((eRR (ℝ × ℝ) z).1.2 + (bMRR (eRR (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (3 * N₁) * (3 * N₂) * NMRR θ) := by have := NMRR_nonneg θ; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KMRR.stronglyMeasurable
    ![y4 (fun i => -R₁.y₂ i) R₂.y₂ (-R₁.ε) R₂.ε, y4 R₁.y₁ 0 R₁.ε 0, y4 0 R₂.y₁ 0 R₂.ε] (measurable_csRR (ℝ × ℝ))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y4 (g := (0 : ι₂ → ℤ)) h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign) (show |(0 : ℤ)| ≤ 1 by simp))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KMRR (LsRR (R₁.get p.1) (R₂.get p.2))
      (csRR (ℝ × ℝ)))
    (fun p => symReg_piece_RR_M (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRR (ℝ × ℝ)) (measurePreserving_eRR _) measurable_bMRR hC
    (fun p => norm_piece_RR_M h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_RR_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Fin 2), S.Bound θ A (3 * (16 * (6 * N₁) * (6 * N₂) * NPRR θ)) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPRR (LsRR (R₁.get p.1) (R₂.get p.2)) (csRR Unit) α z *
          jker (bundle (yRRR (ι₁ := ι₁) (R₂.get p.2)) α) ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1)
            ((eRR Unit z).1.2 + (bP1RR (eRR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (6 * N₁) * (6 * N₂) * NPRR θ) := by have := NPRR_nonneg θ; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPRR.stronglyMeasurable
    ![y4 (fun i => -R₁.y₂ i) R₂.y₂ (-R₁.ε) R₂.ε, y4 R₁.y₁ 0 R₁.ε 0, y4 0 R₂.y₁ 0 R₂.ε] (measurable_csRR Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y4 (f := (0 : ι₁ → ℤ)) isBundle_zero h₂.bundle₂ (show |(0 : ℤ)| ≤ 1 by simp) (abs_sign_le h₂.sign))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPRR (LsRR (R₁.get p.1) (R₂.get p.2))
      (csRR Unit))
    (fun p => symReg_piece_RR_P1 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRR Unit) (measurePreserving_eRR _) measurable_bP1RR hC
    (fun p => norm_piece_RR_P1 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_RR_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Fin 2), S.Bound θ A (3 * (16 * (3 * N₁) * (3 * N₂) * NPRR θ)) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, tripleS (R₁.get p.1).m (R₂.get p.2).m KPRRn (LsRR (R₁.get p.1) (R₂.get p.2)) (csRR Unit) α z *
          jker (bundle (yRRL (ι₂ := ι₂) (R₁.get p.1)) α) ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1)
            ((eRR Unit z).1.2 + (bP2RR (eRR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 3 * (16 * (3 * N₁) * (3 * N₂) * NPRR θ) := by have := NPRR_nonneg θ; positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_KPRRn.stronglyMeasurable
    ![y4 (fun i => -R₁.y₂ i) R₂.y₂ (-R₁.ε) R₂.ε, y4 R₁.y₁ 0 R₁.ε 0, y4 0 R₂.y₁ 0 R₂.ε] (measurable_csRR Unit)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_y4 (g := (0 : ι₂ → ℤ)) h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign) (show |(0 : ℤ)| ≤ 1 by simp))
    (a := fun p => tripleS (R₁.get p.1).m (R₂.get p.2).m KPRRn (LsRR (R₁.get p.1) (R₂.get p.2))
      (csRR Unit))
    (fun p => symReg_piece_RR_P2 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eRR Unit) (measurePreserving_eRR _) measurable_bP2RR hC
    (fun p => norm_piece_RR_P2 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

end PiecesRR

end WaveTurbulence.ClassJR
