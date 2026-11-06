/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Engine2
public import WaveTurbulence.Foundations.Spine.Engine3
/-! # Factorization engine (S3b LADDER-DECAY)

`factor_engine`: the time-integral of the constrained rung sum with a product of unit-ball
amplitudes at affine labels is bounded by `(7^d * cellFourierFactor d)^{#bonds}` times the product
over rungs of the supremum, over additive linear phases, of the rung time integrals. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint
open scoped FourierTransform ENNReal

variable {d n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma measurable_nuK (L : ℝ) (lab : ι → AffLab d n) (k : Fin n) (p : Pt d) :
    Measurable (fun ξ : ι → Mom d => nuK L lab ξ k p) := by
  have : Continuous (fun ξ : ι → Mom d => nuK L lab ξ k p) := by
    simp only [nuK, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact continuous_finset_sum _ (fun b _ => (continuous_apply b).inner continuous_const)
  exact this.measurable

lemma measurable_Gmaj (L : ℝ) (lab : ι → AffLab d n) (S : Fin n → Finset (Pt d))
    (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (M : ℕ) (W : Fin n → ℝ × ℝ → Pt d → ℂ)
    (hWm : ∀ k p, Measurable (fun t => W k t p)) :
    Measurable (fun z : (Fin n → ℝ × ℝ) × (ι → Mom d) =>
      Gmaj L lab S Δ M (fun k p => W k (z.1 k) p) z.2) := by
  unfold Gmaj
  refine Measurable.const_mul (Finset.measurable_sum _ (fun j _ => ?_)) _
  refine Finset.measurable_prod _ (fun k _ => ?_)
  refine Measurable.norm (Finset.measurable_sum _ (fun p _ => ?_))
  refine Measurable.mul ((hWm k p).comp ((measurable_pi_apply k).comp measurable_fst)) ?_
  have h1 : Measurable (fun ξ : ι → Mom d => e ((nuK L lab ξ k + psiK M (Δ k) j) p)) := by
    have : ∀ ξ : ι → Mom d, (nuK L lab ξ k + psiK M (Δ k) j) p =
        nuK L lab ξ k p + psiK M (Δ k) j p := fun ξ => rfl
    simp_rw [this]
    unfold e
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul ((measurable_nuK L lab k p).add_const _))).mul_const Complex.I)
  exact h1.comp measurable_snd


/-- One-rung twisted time integrals are bounded, by hypothesis, uniformly in the linear phase. -/
theorem lintegral_Gmaj_le (L : ℝ) (lab : ι → AffLab d n) (S : Fin n → Finset (Pt d))
    (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (M : ℕ) (hM : 0 < M)
    (W : Fin n → ℝ × ℝ → Pt d → ℂ) (hWm : ∀ k p, Measurable (fun t => W k t p))
    (hWb : ∀ k t p, ‖W k t p‖ ≤ 1)
    (box : Fin n → Set (ℝ × ℝ)) (hbox : ∀ k, MeasurableSet (box k))
    (hfin : ∀ k, volume (box k) < ⊤) (B : Fin n → ℝ)
    (hB : ∀ k (ν : Pt d →+ ℝ), ∫ t in box k, ‖∑ p ∈ S k, W k t p * e (ν p)‖ ≤ B k)
    (ξ : ι → Mom d) :
    ∫⁻ t in Set.pi Set.univ box,
      ENNReal.ofReal (Gmaj L lab S Δ M (fun k p => W k (t k) p) ξ) ≤
        ENNReal.ofReal (∏ k, B k) := by
  set r : (Fin d → Fin M) → Fin n → ℝ × ℝ → ℝ := fun j k τ =>
    ‖∑ p ∈ S k, W k τ p * e ((nuK L lab ξ k + psiK M (Δ k) j) p)‖ with hr
  have hrm : ∀ j k, Measurable (r j k) := by
    intro j k
    refine Measurable.norm (Finset.measurable_sum _ (fun p _ => ?_))
    refine Measurable.mul (hWm k p) measurable_const
  have hrb : ∀ j k τ, r j k τ ≤ (S k).card := by
    intro j k τ
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ S k, ‖W k τ p * e ((nuK L lab ξ k + psiK M (Δ k) j) p)‖ ≤ ∑ _p ∈ S k, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          rw [norm_mul, norm_e, mul_one]; exact hWb k τ p
      _ = (S k).card := by simp
  have hpt : ∀ t : Fin n → ℝ × ℝ,
      ENNReal.ofReal (Gmaj L lab S Δ M (fun k p => W k (t k) p) ξ) =
        ENNReal.ofReal (((M : ℝ) ^ d)⁻¹) *
          ∑ j : Fin d → Fin M, ∏ k, ENNReal.ofReal (r j k (t k)) := by
    intro t
    unfold Gmaj
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
      (fun j _ => Finset.prod_nonneg (fun k _ => norm_nonneg _))]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun k _ => norm_nonneg _)]
  simp_rw [hpt]
  have hmeasj : ∀ j : Fin d → Fin M, Measurable (fun t : Fin n → ℝ × ℝ =>
      ∏ k, ENNReal.ofReal (r j k (t k))) := fun j =>
    Finset.measurable_prod _ (fun k _ =>
      ENNReal.measurable_ofReal.comp ((hrm j k).comp (measurable_pi_apply k)))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum' _ (fun j _ => (hmeasj j).aemeasurable)]
  have hj : ∀ j : Fin d → Fin M, ∫⁻ t in Set.pi Set.univ box, ∏ k, ENNReal.ofReal (r j k (t k)) ≤
      ENNReal.ofReal (∏ k, B k) := by
    intro j
    rw [lintegral_pi_box_prod (r j) (hrm j) (fun k t => norm_nonneg _)
      (fun k => (S k).card) (hrb j) box hbox hfin]
    refine ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_))
    · exact integral_nonneg (fun t => norm_nonneg _)
    · exact hB k (nuK L lab ξ k + psiK M (Δ k) j)
  calc ENNReal.ofReal (((M : ℝ) ^ d)⁻¹) * ∑ j : Fin d → Fin M,
        ∫⁻ t in Set.pi Set.univ box, ∏ k, ENNReal.ofReal (r j k (t k)) ≤
      ENNReal.ofReal (((M : ℝ) ^ d)⁻¹) * ∑ _j : Fin d → Fin M, ENNReal.ofReal (∏ k, B k) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ => hj j))
    _ = ENNReal.ofReal (∏ k, B k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        have h1 : ENNReal.ofReal (((M : ℝ) ^ d)⁻¹) * ((M ^ d : ℕ) : ℝ≥0∞) = 1 := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          push_cast
          rw [inv_mul_cancel₀ (by positivity)]
          simp
        rw [h1, one_mul]


/-- **The factorization engine.** -/
theorem factor_engine (hd : 1 ≤ d) (L : ℝ) (base : Mom d) (F : ι → Mom d → ℂ) (ctr : ι → Mom d)
    (lab : ι → AffLab d n)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (S : Fin n → Finset (Pt d)) (W : Fin n → ℝ × ℝ → Pt d → ℂ)
    (hWm : ∀ k p, Measurable (fun t => W k t p)) (hWb : ∀ k t p, ‖W k t p‖ ≤ 1)
    (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (c0 : Fin d → ℤ)
    (box : Fin n → Set (ℝ × ℝ)) (hbox : ∀ k, MeasurableSet (box k))
    (hfin : ∀ k, volume (box k) < ⊤) (B : Fin n → ℝ)
    (hB : ∀ k (ν : Pt d →+ ℝ), ∫ t in box k, ‖∑ p ∈ S k, W k t p * e (ν p)‖ ≤ B k) :
    ∫ t in Set.pi Set.univ box, ‖∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((lab b).eval P))) * ∏ k, W k (t k) (P k) else 0)‖ ≤
      (7 ^ d * cellFourierFactor d) ^ Fintype.card ι * ∏ k, B k := by
  obtain ⟨M, hM, hb⟩ := exists_modulus (S := S) Δ c0
  have hBnn : ∀ k, 0 ≤ B k := fun k =>
    (integral_nonneg (fun t => norm_nonneg _)).trans (hB k 0)
  have hcff := cellFourierFactor_nonneg d
  have hRnn : 0 ≤ (7 ^ d * cellFourierFactor d) ^ Fintype.card ι * ∏ k, B k :=
    mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hcff) _)
      (Finset.prod_nonneg (fun k _ => hBnn k))
  set N : (Fin n → ℝ × ℝ) → ℝ := fun t => ‖∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((lab b).eval P))) * ∏ k, W k (t k) (P k) else 0)‖ with hN
  by_cases hI : Integrable N (volume.restrict (Set.pi Set.univ box))
  swap
  · rw [integral_undef hI]; exact hRnn
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun t => norm_nonneg _))
    hI.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hRnn ?_
  -- main estimate
  set A := Fintype.piFinset (fun b => cellsAround (ctr b)) with hA
  set H : (ι → Fin d → ℤ) → (Fin n → ℝ × ℝ) → (ι → Mom d) → ℝ≥0∞ := fun a t ξ =>
    ‖Phi F a ξ‖ₑ * ENNReal.ofReal (Gmaj L lab S Δ M (fun k p => W k (t k) p) ξ) with hH
  have hstep : ∀ t : Fin n → ℝ × ℝ, ENNReal.ofReal (N t) ≤ ∑ a ∈ A, ∫⁻ ξ, H a t ξ := fun t => by
    rw [hN, ofReal_norm_eq_enorm]
    exact stepA hd L base F ctr lab hF hsupp S Δ c0 M hM hb (fun k p => W k (t k) p)
  have hΦm : ∀ a, AEMeasurable (fun ξ : ι → Mom d => ‖Phi F a ξ‖ₑ) := fun a =>
    (amp_expansion_mass hd F hF a).1.aestronglyMeasurable.enorm
  have hHm : ∀ a, AEMeasurable (Function.uncurry (H a))
      ((volume.restrict (Set.pi Set.univ box)).prod volume) := by
    intro a
    have h1 : AEMeasurable (fun z : (Fin n → ℝ × ℝ) × (ι → Mom d) => ‖Phi F a z.2‖ₑ)
        ((volume.restrict (Set.pi Set.univ box)).prod volume) :=
      (hΦm a).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable (fun z : (Fin n → ℝ × ℝ) × (ι → Mom d) =>
        ENNReal.ofReal (Gmaj L lab S Δ M (fun k p => W k (z.1 k) p) z.2)) :=
      ENNReal.measurable_ofReal.comp (measurable_Gmaj L lab S Δ M W hWm)
    exact h1.mul h2.aemeasurable
  calc ∫⁻ t in Set.pi Set.univ box, ENNReal.ofReal (N t)
      ≤ ∫⁻ t in Set.pi Set.univ box, ∑ a ∈ A, ∫⁻ ξ, H a t ξ := lintegral_mono hstep
    _ = ∑ a ∈ A, ∫⁻ t in Set.pi Set.univ box, ∫⁻ ξ, H a t ξ := by
        refine lintegral_finsetSum' _ (fun a _ => ?_)
        exact (hHm a).lintegral_prod_right'
    _ = ∑ a ∈ A, ∫⁻ ξ, ∫⁻ t in Set.pi Set.univ box, H a t ξ := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact lintegral_lintegral_swap (hHm a)
    _ ≤ ∑ a ∈ A, ∫⁻ ξ, ‖Phi F a ξ‖ₑ * ENNReal.ofReal (∏ k, B k) := by
        refine Finset.sum_le_sum (fun a _ => lintegral_mono (fun ξ => ?_))
        rw [hH]
        dsimp only
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul' le_rfl (lintegral_Gmaj_le L lab S Δ M hM W hWm hWb box hbox hfin B hB ξ)
    _ ≤ ∑ _a ∈ A, ENNReal.ofReal (cellFourierFactor d ^ Fintype.card ι) *
          ENNReal.ofReal (∏ k, B k) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine mul_le_mul' ?_ le_rfl
        obtain ⟨hint, hmass⟩ := amp_expansion_mass hd F hF a
        have hint' : Integrable (fun ξ : ι → Mom d => Phi F a ξ) := hint
        have := ofReal_integral_norm_eq_lintegral_enorm hint'
        rw [← this]
        exact ENNReal.ofReal_le_ofReal hmass
    _ ≤ ENNReal.ofReal ((7 ^ d * cellFourierFactor d) ^ Fintype.card ι * ∏ k, B k) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hcard : (A.card : ℝ) ≤ (7 ^ d) ^ Fintype.card ι := by
          rw [hA, Fintype.card_piFinset]
          have : ∏ b : ι, (cellsAround (ctr b)).card ≤ ∏ _b : ι, 7 ^ d :=
            Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun b _ => card_cellsAround _)
          calc ((∏ b : ι, (cellsAround (ctr b)).card : ℕ) : ℝ) ≤ ((∏ _b : ι, 7 ^ d : ℕ) : ℝ) := by
                exact_mod_cast this
            _ = (7 ^ d) ^ Fintype.card ι := by simp
        have hB0 : 0 ≤ ∏ k, B k := Finset.prod_nonneg (fun k _ => hBnn k)
        rw [mul_pow, mul_assoc]
        calc (A.card : ℝ) * (cellFourierFactor d ^ Fintype.card ι * ∏ k, B k)
            ≤ (7 ^ d) ^ Fintype.card ι * (cellFourierFactor d ^ Fintype.card ι * ∏ k, B k) :=
              mul_le_mul_of_nonneg_right hcard (mul_nonneg (pow_nonneg hcff _) hB0)
          _ = _ := by ring

end WaveTurbulence.LadderDecay
