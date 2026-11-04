/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainId

/-!
# One term of a chain with a bottom coefficient

DH21 L1137–L1150. For a term of `chainT_bottom_expand` with masks `Y' ⊆ Y ⊆ adj`, a Lemma G piece
`G_Y(z, λ₀; α, t) = ∫ H(z, λ₀; α ∘ f_H, ξ) e^{πi fr(ξ) t} dξ` (`LGPiece`), and the differences
`D = Y ∖ Y'` attached to the pair symbols (`chainP`), the integral of the term over the frequencies
`(z, λ)` is the time integral of the coefficient symbol `Cassem` (`chainTerm`), which has the DH23
bounds by `srep_assemble`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Term

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ}

/-- The variables of a chain term: the pair symbols with the differences, the bottom symbol, and
the variables of the Lemma G piece. -/
@[expose] noncomputable def fTerm (P : ℕ → PSym V) (c : LegalCode) (D : Finset ℕ) {ιb ιH : Type}
    (fb : ιb → V) (fH : ιH → V) : (ιT (chainP P σ ε D) c 0 ⊕ ιb) ⊕ ιH → V :=
  Sum.elim (Sum.elim (fT (chainP P σ ε D) c 0) fb) fH

/-- **One term of a chain with a bottom coefficient** (DH21 L1137–L1150). -/
theorem chainTerm {θ a b A NT Nb NH : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1) {c : LegalCode}
    (hinj : Set.InjOn σ (Set.Ico 0 c.size)) {P : ℕ → PSym V} {Y Y' : Finset ℕ}
    (hD : Y \ Y' ⊆ Finset.Ico 0 (0 + c.size))
    (hT : TBound A NT b c 0 (MzS (chainP P σ ε (Y \ Y')) c 0))
    {ιb : Type} [Fintype ιb] {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ}
    (hCb : SRep θ a b A Nb Cb)
    {ιH : Type} [Fintype ιH] {fH : ιH → V} {Ξ : Type} [MeasureSpace Ξ]
    [SFinite (volume : Measure Ξ)] {bfr : Ξ → ℝ} (hbfr : Measurable bfr)
    {H : ZT c → ℝ → (ιH → ℝ) → ℝ × Ξ → ℂ} (hNH : 0 ≤ NH)
    (hH : ∀ p L0, FRep θ a b A NH (fun ξ => ξ.1 + bfr ξ.2) (H p L0))
    (hHm : Measurable fun x : (ZT c × ℝ) × ((ιH → ℝ) × (ℝ × Ξ)) => H x.1.1 x.1.2 x.2.1 x.2.2)
    {jH : ιH → ℕ} (hjH : ∀ i, jH i ∈ Set.Ico 0 c.size ∧ fH i = σ (jH i))
    {Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ}
    (hGp : ∀ p L0 α, ∀ t ∈ Icc (0 : ℝ) 1,
      Gp p L0 α t = ∫ ξ, H p L0 (α ∘ fH) ξ * cexp (π * I * ((ξ.1 + bfr ξ.2) * t))) :
    SRep θ a b A (4 * (4 * NT * Nb) * NH)
        (Cassem (pprod (MzS (chainP P σ ε (Y \ Y')) c 0) Cb) H bfr (sV σ ε c fH)) ∧
      ∀ α : V → ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s : ℝ,
        Integrable (gTerm σ ε P fb Cb c Gp Y Y' α t s) ∧
          ∫ w, gTerm σ ε P fb Cb c Gp Y Y' α t s w =
            ∫ lam, Cassem (pprod (MzS (chainP P σ ε (Y \ Y')) c 0) Cb) H bfr (sV σ ε c fH)
              (α ∘ fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH) lam * e2 lam t s := by
  classical
  set D := Y \ Y' with hD_def
  set P' := chainP P σ ε D with hP'
  obtain ⟨hMn, hMv, hMf⟩ := chainM_bounds hT hCb hθ ha haθ hA
  have hvH : ∀ i, Measurable fun w' : ZT c => ((1 : ℝ≥0∞) + ‖(Λz c 0 w' (jH i)).1‖ₑ) ^ b :=
    fun i => ((measurable_fst.comp (continuous_Λz c 0 (jH i)).measurable).enorm.const_add
      1).pow_const b
  obtain ⟨hS, hreg, hid⟩ := srep_assemble (M := pprod (MzS P' c 0) Cb) (H := H) (bfr := bfr)
    (sH := sV σ ε c fH) hθ ha haθ hb hA (contDiff_pprod hT.smooth hCb.reg.smooth)
    (measurable_pprod hT.meas hCb.reg.meas) (by have := hT.nonneg; have := hCb.nonneg; positivity)
    hMn hMv (vH := fun i w' => ((1 : ℝ≥0∞) + ‖(Λz c 0 w' (jH i)).1‖ₑ) ^ b) hvH
    (fun i => hMf (jH i)) hbfr hNH hH hHm (measurable_sV fH)
    (fun w' i => one_add_sV_le hε hinj (hjH i).1 (hjH i).2 w')
  refine ⟨hS, fun α t ht s => ?_⟩
  set Ĉ : ℕ → ℝ × ℝ → ℂ := fun j => (P j).C (α ∘ (P j).f) with hĈ
  set β := α ∘ fTerm (σ := σ) (ε := ε) P c D fb fH with hβ
  set F : (ZT c × (ℝ × ℝ)) × (ℝ × Ξ) → ℂ := fun x =>
    kprod (pprod (MzS P' c 0) Cb) (Kc H (sV σ ε c fH)) β x * e2 (FrA bfr x) t s with hF
  have hFi : Integrable F := by
    refine (hreg.integrable β).mul_bdd (c := 1) ?_ (Eventually.of_forall fun x => (norm_e2 _ t s).le)
    have h1 : Measurable fun x : (ZT c × (ℝ × ℝ)) × (ℝ × Ξ) => FrA bfr x := by
      unfold FrA; fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => e2 p t s := by unfold e2; fun_prop
    exact (h2.measurable.comp h1).aestronglyMeasurable
  -- the product of the pair symbols
  have hM : ∀ z : ZT c, MzS P' c 0 (α ∘ fT P' c 0) z =
      Mz Ĉ c 0 z * ∏ j ∈ D, Dfun (ε j) (Λz c 0 z j).1 (α (σ j)) := by
    intro z
    rw [← Mz_eq_MzS]
    have e : (fun j => (P' j).C (α ∘ (P' j).f)) =
        fun j lam => Ĉ j lam * (if j ∈ D then Dfun (ε j) lam.1 (α (σ j)) else 1) := by
      funext j lam
      exact chainP_C α j lam
    rw [e, Mz_mul, Finset.prod_ite_mem, Finset.inter_eq_right.2 hD]
  -- the integral over the Lemma G variables
  have hpt : ∀ w : ZT c × (ℝ × ℝ), ∫ ξ, F (w, ξ) = gTerm σ ε P fb Cb c Gp Y Y' α t s w := by
    intro w
    have e1 : ∀ ξ : ℝ × Ξ, F (w, ξ) =
        (Mz Ĉ c 0 w.1 * (∏ j ∈ D, Dfun (ε j) (Λz c 0 w.1 j).1 (α (σ j))) *
          (Cb (α ∘ fb) w.2 * cexp (π * I * (w.2.2 * s)))) *
        (H w.1 w.2.1 (shiftV σ ε (Λz c 0 w.1) 0 c.size α ∘ fH) ξ *
          cexp (π * I * ((ξ.1 + bfr ξ.2) * t))) := by
      intro ξ
      have e2' : F (w, ξ) = (MzS P' c 0 (α ∘ fT P' c 0) w.1 * Cb (α ∘ fb) w.2) *
          H w.1 w.2.1 (α ∘ fH + sV σ ε c fH w.1) ξ * e2 (ξ.1 + bfr ξ.2, w.2.2) t s := rfl
      rw [e2', hM, ← shiftV_comp, e2_split]
      dsimp only
      push_cast
      ring
    simp_rw [e1]
    rw [integral_const_mul, ← hGp w.1 w.2.1 _ t ht]
    simp only [gTerm, hĈ, hD_def]
    ring
  refine ⟨(hFi.integral_prod_left).congr (Eventually.of_forall hpt), ?_⟩
  rw [hid β t s]
  have e3 : ∫ x, F x = ∫ w, ∫ ξ, F (w, ξ) := integral_prod _ hFi
  rw [show (∫ x, kprod (pprod (MzS P' c 0) Cb) (Kc H (sV σ ε c fH)) β x * e2 (FrA bfr x) t s) =
    ∫ x, F x from rfl, e3]
  exact integral_congr_ae (Eventually.of_forall fun w => (hpt w).symm)

end Term

end WaveTurbulence.ClassJR
