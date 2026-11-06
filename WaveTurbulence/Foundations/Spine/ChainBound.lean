/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Engine4
public import WaveTurbulence.Foundations.Spine.RungTotal
public import WaveTurbulence.Foundations.Spine.ChainExpand
public import WaveTurbulence.Foundations.Spine.ChartAff
public import WaveTurbulence.Foundations.Spine.ChainMol
/-! # The abstract chain bound (S3b LADDER-DECAY)

Rung weights that are signed sums of `GoodTerm`s, the unit-ball bond amplitudes and the rung phases
give a time integral bounded by `36^n (7^d c_ff)^{#bonds} ∏_k B_k`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d n : ℕ}

/-- The rung phase at the time pair `τ = (t_v, t_u)`. -/
noncomputable def rungPh (L c : ℝ) (lam : Pt d →+ ℝ) (τ : ℝ × ℝ) (p : Pt d) : ℂ :=
  e (c * (τ.1 - τ.2) * bil L p + τ.1 * lam p)

lemma norm_rungPh (L c : ℝ) (lam : Pt d →+ ℝ) (τ : ℝ × ℝ) (p : Pt d) : ‖rungPh L c lam τ p‖ = 1 :=
  norm_e _

lemma continuous_rungPh (L c : ℝ) (lam : Pt d →+ ℝ) (p : Pt d) :
    Continuous (fun τ : ℝ × ℝ => rungPh L c lam τ p) := by
  unfold rungPh e
  fun_prop

/-- The box of lattice points where the inserted cutoff may be nonzero. -/
noncomputable def cutBox (d : ℕ) (L : ℝ) (a b : Fin d → ℝ) : Finset (Pt d) :=
  Counting.latticeBox (fun j => L * a j) (4 * L) ×ˢ Counting.latticeBox (fun j => L * b j) (4 * L)

lemma cutW_mem_cutBox {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (p : Pt d) (h : cutW L a b p ≠ 0) :
    p ∈ cutBox d L a b := by
  have := cutW_ne_zero_x hL a b p h
  exact Finset.mem_product.mpr this

/-- The labels of the interior bonds as affine functions of the chart. -/
def chainLab (Sg : ChainSigns n) (a0 b0 : Fin d → ℤ) : LadderDarts.Ctx.Code n → AffLab d n
  | .inl (i, k) => rungAff Sg a0 i k
  | .inr (.inl j) => railAff Sg a0 j
  | .inr (.inr j) => railBAff Sg a0 b0 j

/-- The flux-closure functionals. -/
def chainΔ (Sg : ChainSigns n) (k : Fin n) : Pt d →+ (Fin d → ℤ) := tauHom Sg k 2 - tauHom Sg k 3

lemma chainLab_eval (Sg : ChainSigns n) (a0 b0 : Fin d → ℤ) (P : Fin n → Pt d)
    (c : LadderDarts.Ctx.Code n) :
    ((chainLab Sg a0 b0 c).eval P) = (match c with
      | .inl (i, k) => (Sg.inv a0 b0 P).r i k
      | .inr (.inl j) => (Sg.inv a0 b0 P).a j
      | .inr (.inr j) => (Sg.inv a0 b0 P).b j) := by
  rcases c with ⟨i, k⟩ | j | j
  · exact rungAff_eval Sg a0 P i k
  · exact railAff_eval Sg a0 P j
  · exact railBAff_eval Sg a0 b0 P j

lemma GoodTerm.abs_le {L R : ℝ} {a b : Fin d → ℝ} {χ : Pt d → ℝ} (h : GoodTerm L R a b χ) : ∀ p, |χ p| ≤ 1 := by
  rcases h with h | h | h | h
  · intro p; rw [h p]; simp
  · exact h.abs_le
  · exact h.abs_le
  · exact h.1

lemma rung_term_eq (L c : ℝ) (wgt : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) (τ : ℝ × ℝ) :
    ∑ p ∈ S, (wgt p * rungPh L c lam τ p) * e (ν p) = rungSum L c wgt S lam ν (τ.2, τ.1) := by
  unfold rungSum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_assoc]
  unfold rungPh
  rw [← e_add]
  congr 2
  simp only
  ring

lemma continuous_rung_term (L c : ℝ) (wgt : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) :
    Continuous (fun τ : ℝ × ℝ => ∑ p ∈ S, (wgt p * rungPh L c lam τ p) * e (ν p)) := by
  refine continuous_finset_sum _ (fun p _ => ?_)
  exact (continuous_const.mul (continuous_rungPh L c lam p)).mul continuous_const

lemma box_integral_eq (L c : ℝ) (wgt : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ)
    (l u v w : ℝ) :
    (∫ τ in Icc v w ×ˢ Icc l u, ‖∑ p ∈ S, (wgt p * rungPh L c lam τ p) * e (ν p)‖) =
      ∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L c wgt S lam ν (s, t)‖ := by
  rw [Measure.volume_eq_prod, setIntegral_prod]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only
    rw [rung_term_eq]
  · have hc := (continuous_rung_term L c wgt S lam ν).norm
    rw [← Measure.volume_eq_prod]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

section chain
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma continuous_chain_sum (L c : ℝ) (lam : Fin n → Pt d →+ ℝ) (SP : Fin n → Finset (Pt d))
    (cond : (Fin n → Pt d) → Prop) [DecidablePred cond] (Φ : (Fin n → Pt d) → ℂ)
    (A : Fin n → Pt d → ℂ) :
    Continuous (fun τ : Fin n → ℝ × ℝ => ∑ P ∈ Fintype.piFinset SP, (if cond P then
      Φ P * ∏ k, (A k (P k) * rungPh L c (lam k) (τ k) (P k)) else 0)) := by
  refine continuous_finset_sum _ (fun P _ => ?_)
  by_cases hc : cond P
  · simp only [hc, if_true]
    refine continuous_const.mul (continuous_finset_prod _ (fun k _ => ?_))
    exact continuous_const.mul ((continuous_rungPh L c (lam k) (P k)).comp (continuous_apply k))
  · simp only [hc, if_false]; exact continuous_const

/-- Pointwise reduction of the full weight to the choices of one term per rung. -/
lemma chain_pointwise (L c : ℝ) (ca cb : Fin n → Fin d → ℝ) (lam : Fin n → Pt d →+ ℝ) (Sg : ChainSigns n) (c0 : Fin d → ℤ)
    (Φ : (Fin n → Pt d) → ℂ) (s : Fin n → J → ℝ) (χ : Fin n → J → Pt d → ℝ)
    (hcut : ∀ P, Φ P ≠ 0 → ∀ k, cutW L (ca k) (cb k) (P k) = 1) (τ : Fin n → ℝ × ℝ) :
    ∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        Φ P * ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) * rungPh L c (lam k) (τ k) (P k)) else 0) =
      ∑ α : Fin n → J, (∏ k, ((s k (α k) : ℝ) : ℂ)) *
        ∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
          Φ P * ∏ k, (((χ k (α k) (P k) : ℝ) : ℂ) * cutW L (ca k) (cb k) (P k) *
            rungPh L c (lam k) (τ k) (P k)) else 0) :=
  expand_rung_sum (fun k => cutBox d L (ca k) (cb k)) (fun P => ∑ k, chainΔ Sg k (P k) = c0) Φ s χ
    (fun k p => rungPh L c (lam k) (τ k) p) (fun k => cutW L (ca k) (cb k)) hcut

end chain

section engineApp

/-- One choice of rung terms: the engine bound. -/
lemma engine_alpha (hd : 1 ≤ d) {L c : ℝ} (ca cb : Fin n → Fin d → ℝ) (Sg : ChainSigns n) (a0 b0 c0 : Fin d → ℤ) (base : Mom d)
    (F : LadderDarts.Ctx.Code n → Mom d → ℂ) (ctr : LadderDarts.Ctx.Code n → Mom d)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (χ' : Fin n → Pt d → ℝ) (hχa : ∀ k p, |χ' k p| ≤ 1) (lam : Fin n → Pt d →+ ℝ)
    (l u v w : Fin n → ℝ) (B : Fin n → ℝ)
    (hint : ∀ k (ν : Pt d →+ ℝ), (∫ t in Icc (v k) (w k), ∫ s in Icc (l k) (u k),
      ‖rungSum L c (fun p => ((χ' k p : ℝ) : ℂ) * cutW L (ca k) (cb k) p) (cutBox d L (ca k) (cb k)) (lam k) ν (s, t)‖) ≤ B k) :
    ∫ τ in Set.pi Set.univ (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k)),
      ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P))) *
          ∏ k, (((χ' k (P k) : ℝ) : ℂ) * cutW L (ca k) (cb k) (P k) * rungPh L c (lam k) (τ k) (P k)) else 0)‖ ≤
      (7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) * ∏ k, B k := by
  refine factor_engine hd L base F ctr (chainLab Sg a0 b0) hF hsupp (fun k => cutBox d L (ca k) (cb k))
    (fun k τ p => ((χ' k p : ℝ) : ℂ) * cutW L (ca k) (cb k) p * rungPh L c (lam k) τ p) ?_ ?_
    (chainΔ Sg) c0 (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k)) (fun k => measurableSet_Icc.prod measurableSet_Icc)
    (fun k => ?_) B ?_
  · intro k p
    exact (continuous_const.mul (continuous_rungPh L c (lam k) p)).measurable
  · intro k τ p
    rw [norm_mul, norm_mul, norm_rungPh, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (hχa k p) (norm_nonneg _) (norm_cutW_le L (ca k) (cb k) p)
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp only [Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · intro k ν
    have := box_integral_eq L c (fun p => ((χ' k p : ℝ) : ℂ) * cutW L (ca k) (cb k) p) (cutBox d L (ca k) (cb k)) (lam k) ν
      (l k) (u k) (v k) (w k)
    exact this.trans_le (hint k ν)

end engineApp

/-- The per-rung budget (same layer: `δ⁻¹ E`; different layers: with the extra `L^{-x}`). -/
noncomputable def rungBudget (d : ℕ) (γ x δ L C0 : ℝ) (diff : Prop) [Decidable diff] : ℝ :=
  C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * (if diff then L ^ (-x) else 1))

lemma RungOK.integral_le {γ x T1 δ L C0 : ℝ} {a b : Fin d → ℝ} {χ : Pt d → ℝ} (h : RungOK γ x T1 δ L C0 a b χ)
    (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) (l u v w : ℝ)
    (hS : ∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ S) (hlu : l ≤ u) (hvw : v ≤ w)
    (hul : u - l ≤ 1) (hwv : w - v ≤ 1) (hwin : WindowOK T1 L (δ * L ^ (2 * γ)) l u v w γ)
    [Decidable (u ≤ v ∨ w ≤ l)] :
    (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L (δ * L ^ (2 * γ))
          (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) S lam ν (s, t)‖) ≤
      rungBudget d γ x δ L C0 (u ≤ v ∨ w ≤ l) := by
  obtain ⟨h1, h2⟩ := h S lam ν l u v w hS hlu hvw hul hwv hwin
  unfold rungBudget
  by_cases hd : u ≤ v ∨ w ≤ l
  · simp only [hd, if_true]; exact h2 hd
  · simp only [hd, if_false, mul_one]; exact h1

/-- **The abstract chain bound.** -/
theorem chain_bound {J : Type*} [Fintype J] [DecidableEq J] (hd : 1 ≤ d) {γ x T1 δ L C0 : ℝ} (hL : 0 < L) (ca cb : Fin n → Fin d → ℝ) (Sg : ChainSigns n)
    (a0 b0 c0 : Fin d → ℤ) (base : Mom d)
    (F : LadderDarts.Ctx.Code n → Mom d → ℂ) (ctr : LadderDarts.Ctx.Code n → Mom d)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (s : Fin n → J → ℝ) (hs : ∀ k j, |s k j| ≤ 1)
    (χ : Fin n → J → Pt d → ℝ) (hχa : ∀ k j p, |χ k j p| ≤ 1)
    (hχ : ∀ k j, RungOK γ x T1 δ L C0 (ca k) (cb k) (χ k j)) (lam : Fin n → Pt d →+ ℝ) (l u v w : Fin n → ℝ)
    (hlu : ∀ k, l k ≤ u k) (hvw : ∀ k, v k ≤ w k) (hul : ∀ k, u k - l k ≤ 1) (hwv : ∀ k, w k - v k ≤ 1)
    (hwin : ∀ k, WindowOK T1 L (δ * L ^ (2 * γ)) (l k) (u k) (v k) (w k) γ)
    (hcut : ∀ P : Fin n → Pt d,
      (∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P))) ≠ 0 → ∀ k, cutW L (ca k) (cb k) (P k) = 1) :
    ∫ τ in Set.pi Set.univ (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k)),
      ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P))) *
          ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) *
            rungPh L (δ * L ^ (2 * γ)) (lam k) (τ k) (P k)) else 0)‖ ≤
      (Fintype.card J : ℝ) ^ n * ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
        ∏ k, rungBudget d γ x δ L C0 (u k ≤ v k ∨ w k ≤ l k)) := by
  classical
  set c := δ * L ^ (2 * γ) with hc
  set Φ : (Fin n → Pt d) → ℂ := fun P =>
    ∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P)) with hΦ
  set box : Set (Fin n → ℝ × ℝ) := Set.pi Set.univ (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k)) with hbox
  have hcomp : IsCompact box := isCompact_univ_pi (fun k => isCompact_Icc.prod isCompact_Icc)
  set T : (Fin n → J) → (Fin n → ℝ × ℝ) → ℂ := fun α τ =>
    ∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
      Φ P * ∏ k, (((χ k (α k) (P k) : ℝ) : ℂ) * cutW L (ca k) (cb k) (P k) *
        rungPh L c (lam k) (τ k) (P k)) else 0) with hT
  have hTc : ∀ α, Continuous (T α) := fun α =>
    continuous_chain_sum L c lam _ _ Φ (fun k p => ((χ k (α k) p : ℝ) : ℂ) * cutW L (ca k) (cb k) p)
  have hLc : Continuous (fun τ : Fin n → ℝ × ℝ =>
      ∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        Φ P * ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) * rungPh L c (lam k) (τ k) (P k)) else 0)) :=
    continuous_chain_sum L c lam _ _ Φ (fun k p => ((∑ j, s k j * χ k j p : ℝ) : ℂ))
  have hpt : ∀ τ, ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        Φ P * ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) * rungPh L c (lam k) (τ k) (P k)) else 0)‖ ≤
      ∑ α : Fin n → J, ‖T α τ‖ := by
    intro τ
    rw [chain_pointwise L c ca cb lam Sg c0 Φ s χ hcut τ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun α _ => ?_))
    rw [norm_mul]
    have : ‖∏ k, ((s k (α k) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hs k _)
    calc ‖∏ k, ((s k (α k) : ℝ) : ℂ)‖ * ‖T α τ‖ ≤ 1 * ‖T α τ‖ := by gcongr
      _ = _ := one_mul _
  have hint1 : IntegrableOn (fun τ : Fin n → ℝ × ℝ => ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)),
      (if ∑ k, chainΔ Sg k (P k) = c0 then
        Φ P * ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) * rungPh L c (lam k) (τ k) (P k)) else 0)‖) box :=
    hLc.norm.continuousOn.integrableOn_compact hcomp
  have hint2 : ∀ α : Fin n → J, IntegrableOn (fun τ => ‖T α τ‖) box := fun α =>
    (hTc α).norm.continuousOn.integrableOn_compact hcomp
  have hB : ∀ α : Fin n → J, (∫ τ in box, ‖T α τ‖) ≤
      (7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
        ∏ k, rungBudget d γ x δ L C0 (u k ≤ v k ∨ w k ≤ l k) := by
    intro α
    refine engine_alpha hd ca cb Sg a0 b0 c0 base F ctr hF hsupp (fun k => χ k (α k)) (fun k => hχa k (α k))
      lam l u v w (fun k => rungBudget d γ x δ L C0 (u k ≤ v k ∨ w k ≤ l k)) ?_
    intro k ν
    exact (hχ k (α k)).integral_le (cutBox d L (ca k) (cb k)) (lam k) ν (l k) (u k) (v k) (w k)
      (fun p hp => cutW_mem_cutBox hL (ca k) (cb k) p (right_ne_zero_of_mul hp)) (hlu k) (hvw k) (hul k) (hwv k) (hwin k)
  calc _ ≤ ∫ τ in box, ∑ α : Fin n → J, ‖T α τ‖ :=
        integral_mono hint1 (integrable_finsetSum _ (fun α _ => hint2 α)) hpt
    _ = ∑ α : Fin n → J, ∫ τ in box, ‖T α τ‖ := integral_finsetSum _ (fun α _ => hint2 α)
    _ ≤ ∑ _α : Fin n → J, ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
        ∏ k, rungBudget d γ x δ L C0 (u k ≤ v k ∨ w k ≤ l k)) :=
        Finset.sum_le_sum (fun α _ => hB α)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end WaveTurbulence.LadderDecay
