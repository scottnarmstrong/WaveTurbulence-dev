/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.KernelCore
public import WaveTurbulence.Foundations.Flower.LadFilt.RungRect

/-! # C3 LAD-FILT: the chain and class bounds on translated boxes

Copy-threads of main's `chain_bound` (Spine/ChainBound) and `LadderDarts.Ctx.class_bound` (Spine/KernelCore):
the rung boxes are arbitrary rectangles (here the unit layer intervals translated by `τ_v k, τ_u k`), and the
per-rung budget is supplied by `rung_rect_T`. The proof of `class_bound_T` is main's `class_bound` verbatim
except for the last step (copy recorded in `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.WeylSums
  WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d n : ℕ}

/-- **The abstract chain bound on arbitrary rung rectangles** (main's `chain_bound`, with the rung budget
supplied directly for each rung rectangle). -/
theorem chain_bound_T {J : Type*} [Fintype J] [DecidableEq J] (hd : 1 ≤ d) {L c : ℝ} (hL : 0 < L)
    (ca cb : Fin n → Fin d → ℝ) (Sg : ChainSigns n) (a0 b0 c0 : Fin d → ℤ) (base : Mom d)
    (F : LadderDarts.Ctx.Code n → Mom d → ℂ) (ctr : LadderDarts.Ctx.Code n → Mom d)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (s : Fin n → J → ℝ) (hs : ∀ k j, |s k j| ≤ 1)
    (χ : Fin n → J → Pt d → ℝ) (hχa : ∀ k j p, |χ k j p| ≤ 1) (lam : Fin n → Pt d →+ ℝ)
    (l u v w : Fin n → ℝ) (B : Fin n → ℝ)
    (hB : ∀ k j (ν : Pt d →+ ℝ), ∫ τ in Icc (v k) (w k) ×ˢ Icc (l k) (u k),
      ‖∑ p ∈ cutBox d L (ca k) (cb k),
        (((χ k j p : ℝ) : ℂ) * cutW L (ca k) (cb k) p * rungPh L c (lam k) τ p) * e (ν p)‖ ≤ B k)
    (hcut : ∀ P : Fin n → Pt d,
      (∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P))) ≠ 0 →
        ∀ k, cutW L (ca k) (cb k) (P k) = 1) :
    ∫ τ in Set.pi Set.univ (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k)),
      ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)), (if ∑ k, chainΔ Sg k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((chainLab Sg a0 b0 b).eval P))) *
          ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) *
            rungPh L c (lam k) (τ k) (P k)) else 0)‖ ≤
      (Fintype.card J : ℝ) ^ n * ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
        ∏ k, B k) := by
  classical
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
  have hpt : ∀ τ, ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)),
      (if ∑ k, chainΔ Sg k (P k) = c0 then
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
  have hint1 : IntegrableOn (fun τ : Fin n → ℝ × ℝ =>
      ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)),
      (if ∑ k, chainΔ Sg k (P k) = c0 then
        Φ P * ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) * rungPh L c (lam k) (τ k) (P k)) else 0)‖) box :=
    hLc.norm.continuousOn.integrableOn_compact hcomp
  have hint2 : ∀ α : Fin n → J, IntegrableOn (fun τ => ‖T α τ‖) box := fun α =>
    (hTc α).norm.continuousOn.integrableOn_compact hcomp
  have hBα : ∀ α : Fin n → J, (∫ τ in box, ‖T α τ‖) ≤
      (7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) * ∏ k, B k := by
    intro α
    refine factor_engine hd L base F ctr (chainLab Sg a0 b0) hF hsupp (fun k => cutBox d L (ca k) (cb k))
      (fun k τ p => ((χ k (α k) p : ℝ) : ℂ) * cutW L (ca k) (cb k) p * rungPh L c (lam k) τ p) ?_ ?_
      (chainΔ Sg) c0 (fun k => Icc (v k) (w k) ×ˢ Icc (l k) (u k))
      (fun k => measurableSet_Icc.prod measurableSet_Icc) (fun k => ?_) B (fun k ν => hB k (α k) ν)
    · intro k p
      exact (continuous_const.mul (continuous_rungPh L c (lam k) p)).measurable
    · intro k τ p
      rw [norm_mul, norm_mul, norm_rungPh, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_one₀ (hχa k (α k) p) (norm_nonneg _) (norm_cutW_le L (ca k) (cb k) p)
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp only [Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  calc _ ≤ ∫ τ in box, ∑ α : Fin n → J, ‖T α τ‖ :=
        integral_mono hint1 (integrable_finsetSum _ (fun α _ => hint2 α)) hpt
    _ = ∑ α : Fin n → J, ∫ τ in box, ‖T α τ‖ := integral_finsetSum _ (fun α _ => hint2 α)
    _ ≤ ∑ _α : Fin n → J, ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
        ∏ k, B k) := Finset.sum_le_sum (fun α _ => hBα α)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

variable {G : Garden w}

section classT
open WaveTurbulence.LadderDecay.LadderDarts.Ctx
variable {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDecay.LadderDarts.Ctx G.molecule u v)

open scoped Classical in
include C in
/-- **One class, translated rung boxes** (main's `class_bound` with the rung box of rung `k` translated by
`(τ_v k, τ_u k)` and the budget of `rung_rect_T`). -/
theorem class_bound_T (hP : G.IsPlain) {L : ℝ} (hL1 : 1 ≤ L) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (hd : 1 ≤ d)
    (γ η δ x T1 C0 : ℝ) (hδ : 0 < δ) (hx0 : 0 ≤ x) (hC0 : 0 ≤ C0) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η))
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x T1 δ L C0 a b χ)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x))
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 2) ≤ T1) (τv τu : Fin n → ℝ)
    (boundary : GardenDart G → (Fin d → ℤ))
    (T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hTw : ∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0)
    (hTz : ∀ z, z ∉ T → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0)
    (zs : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)) (hzs : zs ∈ T) :
    ∃ H : (Fin n → ℝ × ℝ) → ℝ, Continuous H ∧
      (∀ t : (Molecule.ladderAtoms u v) → ℝ,
        ‖∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
            bondIndex G z.1.1 x = bondIndex G zs.1.1 x),
          ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
            ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤ H (tauOf (u := u) (v := v) t)) ∧
      ∫ σ in Set.pi Set.univ (fun k : Fin n =>
          Icc ((D.layer (v (LadderDarts.ir k)) : ℝ) + τv k) ((D.layer (v (LadderDarts.ir k)) : ℝ) + τv k + 1) ×ˢ
          Icc ((D.layer (u (LadderDarts.ir k)) : ℝ) + τu k) ((D.layer (u (LadderDarts.ir k)) : ℝ) + τu k + 1)),
          H σ ≤
        (Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
          ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
            ∏ k : Fin n, (rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d)
              (D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) *
              rungWt (δ * L ^ (2 * γ) / 2) (τv k) (τu k))) := by
  have hL0 : 0 < L := by linarith
  have hL : L ≠ 0 := hL0.ne'
  have hsz := C.isSol_dec hP hL base roots hn zs.1
  set a0s := (C.chainOf (bondIndex G zs.1.1)).a 0 with ha0s
  set b0s := (C.chainOf (bondIndex G zs.1.1)).b 0 with hb0s
  set q := a0s - b0s with hq
  set c0 := (C.chainOf (bondIndex G zs.1.1)).a (Fin.last n) - a0s with hc0
  set ca : Fin n → (Fin d → ℝ) := fun k => (pairCentres C.signs (C.edgeCtr D) k).1 with hca
  set cb : Fin n → (Fin d → ℝ) := fun k => (pairCentres C.signs (C.edgeCtr D) k).2 with hcb
  have hGS : ∀ k, GoodSum L (L ^ (1 - γ + η)) (ca k) (cb k) ((Fin 3 × Fin 2) × (Fin 3 × Fin 2))
      (C.rungW D L γ η k q) := fun k => C.rungW_goodSum D γ η L _ hL0 hρ hR k q
  choose s χ hs hχ hw using hGS
  have hχabs : ∀ k j p, |χ k j p| ≤ 1 := fun k j p => (hχ k j).abs_le p
  have hRungk : ∀ k j, RungOK γ x T1 δ L C0 (ca k) (cb k) (χ k j) := fun k j => hRung _ _ _ (hχ k j)
  set lam : Fin n → Pt d →+ ℝ := fun k => lamHom L (δ * L ^ (2 * γ)) C.signs k
    (C.signs.qrel (C.chainOf (bondIndex G zs.1.1)) k) with hlam
  have hcut : ∀ P : Fin n → Pt d,
      (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) ≠ 0 →
      ∀ k, cutW L (ca k) (cb k) (P k) = 1 := by
    intro P hP0 k
    have hball : ∀ c, ‖base + latticePoint L (LadderDarts.Ctx.labOf (C.signs.inv a0s b0s P) c) -
        C.edgeCtr D c‖ ≤ 1 := by
      intro c
      by_contra hcon
      push_neg at hcon
      apply hP0
      refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
      rw [chainLab_eval_labOf]
      exact C.edgeF_supp D hD c _ hcon
    exact pair_cutW_eq_one C.signs (C.edgeCtr D) hL0 base a0s b0s P hball k
  set Hf : (Fin n → ℝ × ℝ) → ℝ := fun τ => ‖∑ P ∈ Fintype.piFinset (fun k => cutBox d L (ca k) (cb k)),
      (if ∑ k, chainΔ C.signs k (P k) = c0 then
        (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
          (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) *
          ∏ k, (((∑ j, s k j * χ k j (P k) : ℝ) : ℂ) *
            rungPh L (δ * L ^ (2 * γ)) (lam k) (τ k) (P k)) else 0)‖ with hHf
  refine ⟨Hf, ?_, ?_, ?_⟩
  · exact (continuous_chain_sum L (δ * L ^ (2 * γ)) lam _ _
      (fun P => ∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P)))
      (fun k p => ((∑ j, s k j * χ k j p : ℝ) : ℂ))).norm
  · intro t
    set f : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) → ℂ := fun z =>
      ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t with hf
    set θ := C.classTheta D L γ η δ base roots zs.1 t with hθdef
    set g : (Fin n → Pt d) → ℂ := fun P =>
      (∏ c : LadderDarts.Ctx.Code n, C.edgeF D c
        (base + latticePoint L ((chainLab C.signs a0s b0s c).eval P))) *
      ∏ k : Fin n, (((C.rungW D L γ η k q (P k) : ℝ) : ℂ) *
        rungPh L (δ * L ^ (2 * γ)) (lam k) (tauOf (u := u) (v := v) t k) (P k)) with hg
    have hfac : ∀ z : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
        (∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1.1 x = bondIndex G zs.1.1 x) →
          f z = θ * g (C.signs.pairs (C.chainOf (bondIndex G z.1.1))) := by
      intro z hz
      have := C.weight_phase_factor hP hL base roots hn D γ η δ z.1 zs.1 hz t
      simp only [hf]
      rw [this, mul_assoc]
      rfl
    have hfz : f zs ≠ 0 := by
      simp only [hf]
      refine mul_ne_zero (hTw zs hzs) ?_
      intro h0
      have := norm_ladderPhase D (Molecule.ladderAtoms u v) L γ δ base zs.1.1 t
      rw [h0] at this; simp at this
    have hθ0 : θ ≠ 0 := by
      intro h0
      apply hfz
      rw [hfac zs (fun _ _ => rfl), h0, zero_mul]
    have hgsupp : ∀ P, g P ≠ 0 → ∀ k, P k ∈ cutBox d L (ca k) (cb k) := by
      intro P hP0 k
      have h1 := left_ne_zero_of_mul hP0
      have h2 := hcut P h1 k
      exact cutW_mem_cutBox hL0 _ _ _ (by rw [h2]; exact one_ne_zero)
    have hsum := C.fibre_sum hP hL base roots hn boundary T f
      (fun z hz => by simp only [hf]; rw [hTz z hz, zero_mul]) zs hzs θ g hθ0 hfac
      (fun k => cutBox d L (ca k) (cb k)) hgsupp
    have hnorm := C.norm_classTheta_le D hD L γ η δ base roots zs.1 t
    calc ‖∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
            bondIndex G z.1.1 x = bondIndex G zs.1.1 x),
          ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
            ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖
        = ‖θ * ∑ P ∈ (Fintype.piFinset (fun k => cutBox d L (ca k) (cb k))).filter
            (fun P => ∑ k, chainΔ C.signs k (P k) = c0), g P‖ := by rw [← hsum]
      _ ≤ ‖∑ P ∈ (Fintype.piFinset (fun k => cutBox d L (ca k) (cb k))).filter
            (fun P => ∑ k, chainΔ C.signs k (P k) = c0), g P‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hnorm
      _ = Hf (tauOf (u := u) (v := v) t) := by
          rw [Finset.sum_filter]
          simp only [hHf]
          congr 1
          refine Finset.sum_congr rfl (fun P _ => ?_)
          by_cases hc : ∑ k, chainΔ C.signs k (P k) = c0
          · simp only [hc, if_true, hg]
            congr 1
            refine Finset.prod_congr rfl (fun k _ => ?_)
            rw [hw k (P k)]
          · simp [hc]
  · exact chain_bound_T (J := (Fin 3 × Fin 2) × (Fin 3 × Fin 2)) hd hL0 ca cb C.signs a0s b0s c0 base
      (C.edgeF D) (C.edgeCtr D) (C.edgeF_snorm D hD) (C.edgeF_supp D hD) s hs χ hχabs lam
      (fun k => (D.layer (u (LadderDarts.ir k)) : ℝ) + τu k)
      (fun k => (D.layer (u (LadderDarts.ir k)) : ℝ) + τu k + 1)
      (fun k => (D.layer (v (LadderDarts.ir k)) : ℝ) + τv k)
      (fun k => (D.layer (v (LadderDarts.ir k)) : ℝ) + τv k + 1)
      (fun k => rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d)
        (D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) *
        rungWt (δ * L ^ (2 * γ) / 2) (τv k) (τu k))
      (fun k j ν => rung_rect_T (hRungk k j) (hχabs k j) hL1 hδ hx0 hC0 hB _ _ (hlay _) (hlay _)
        (τv k) (τu k) (lam k) ν) hcut

end classT
end WaveTurbulence.Flower.LadFilt
