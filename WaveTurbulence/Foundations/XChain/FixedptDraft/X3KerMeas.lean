/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3KerInv

/-!
# X3 KerMeas: the masked flower kernels (measurability, phase covariance, FTC, pieces)

Let `b : ℤ^d → ℂ` be data and `b̃ = sumMod b` (`b` if summable, else `0`). For a kind, `†`, cutoffs, `ζ`, `k`,
`k'`, the **masked kernels** are
* `Kpl b t s = 1_{p<s<t≤p+1} 𝒦^{plain}[b̃](t, s, k, k')`;
* `Kdr b u s = 1_{p<s<u<p+1} 𝒦^{dRoot}[b̃](u, s, k, k')`.

**Statement.**
1. `stronglyMeasurable_Kpl`, `stronglyMeasurable_Kdr`: jointly measurable in `(b, t, s)`.
2. `Kpl_mul_phase`, `Kdr_mul_phase`: for a cubic phase `φ`, `Kpl (φ b) = U · Kpl b` with
   `U = φ(0)^{1−ζ} χ(k − ζ k')`, where `χ = \overline{φ(0)} φ` is an additive character (`phaseChar`). So
   `‖Kpl (φ b)‖ = ‖Kpl b‖`, and the same for `Kdr`.
3. `Kpl_FTC`: for summable `b` and `p < s < t₀, t ≤ p + 1`: `Kpl b t s = Kpl b t₀ s + ∫_{t₀}^t Kdr b u s du`.
4. The pieces, masked:
   - `hasSum_Kpl_cut1`, `hasSum_Kpl_cut2`, `hasSum_Kpl_dagger`;
   - the `†` support `Kpl_dagger_eq_zero`;
   - the shift identity `Kpl_shift` (`X3-KerInv`), with the leaf bound `leafMax` of the kind.

**Why.**
- On the masks, the time integrals are the glued integrals of `X3-DerivFl` (`timeInt_plain_eq`, and
  `timeInt_dRoot_eq` with `t = p + 1`). These are jointly measurable in `(t, s)` by `isOpen_domSet`.
- Each decoration term is bounded by `‖∏_{ℓ≠𝔣} b̃_{κ_ℓ}^{ζ_ℓ}‖`, which is summable over decorations.
- For the phase: `∑_{ℓ≠𝔣} ζ_ℓ κ_ℓ = k − ζk'` (momentum), and `∑_{ℓ≠𝔣} ζ_ℓ = 1 − ζ` (the sum rule for the
  constant labelling `1`).
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree

variable {d : ℕ}

/-! ## Glued time integrals, measurable in `(t, s)` -/

section Glue

variable (L γ δ : ℝ) (p : ℕ)

theorem stronglyMeasurable_HT₂ (T : TTree) (off : Finset (GBranch (single T)))
    (κ : GNode (single T) → (Fin d → ℤ)) :
    StronglyMeasurable fun w : ℝ × (GBranch (single T) → ℝ) => HT L γ δ p T off κ w.1 w.2 :=
  ((continuous_phaseOffT L γ δ T off κ).comp continuous_snd).stronglyMeasurable.indicator
    (isOpen_domSet T (p : ℝ)).measurableSet

variable {F : FTree} (hF : F ≠ flower) (off : Finset (GBranch (single F.toTree)))
  (κ : GNode (single F.toTree) → (Fin d → ℤ))

/-- The glued plain time integral (`t_{𝔣^pr} := s`), for all `(t, s)`. -/
noncomputable def TIgPl (t s : ℝ) : ℂ :=
  ∫ σ : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} → ℝ,
    HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s σ)

theorem stronglyMeasurable_TIgPl : StronglyMeasurable fun z : ℝ × ℝ => TIgPl L γ δ p hF off κ z.1 z.2 := by
  have hg : Continuous fun w : (ℝ × ℝ) × ({b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} → ℝ) =>
      ((w.1.1, glueAt (F.flowerParent hF) w.1.2 w.2) : ℝ × (GBranch (single F.toTree) → ℝ)) :=
    continuous_fst.fst.prodMk
      ((continuous_glueAt₂ (F.flowerParent hF)).comp (continuous_fst.snd.prodMk continuous_snd))
  exact ((stronglyMeasurable_HT₂ L γ δ p F.toTree off κ).comp_measurable hg.measurable).integral_prod_right'

theorem TIpat_plain_eq_TIgPl {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1) :
    TIpat L γ δ hF p off κ .plain t s = TIgPl L γ δ p hF off κ t s :=
  timeInt_plain_eq L γ δ hF p off κ hps hst ht

variable (hpr : (F.flowerParent hF).1.2 ≠ [])

/-- The glued `dRoot` time integral (`t_{𝔣^pr} := s`, `t_𝔯 := u`, domain `𝒟(p+1)`), for all `(u, s)`. -/
noncomputable def TIgDr (u s : ℝ) : ℂ :=
  ∫ σ' : {x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // x ≠ rootBr' hF hpr} → ℝ,
    HT L γ δ p F.toTree off κ (p + 1) (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ'))

theorem stronglyMeasurable_TIgDr : StronglyMeasurable fun z : ℝ × ℝ => TIgDr L γ δ p hF off κ hpr z.1 z.2 := by
  have hg : Continuous fun w : (ℝ × ℝ) ×
      ({x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // x ≠ rootBr' hF hpr} → ℝ) =>
      glueAt (F.flowerParent hF) w.1.2 (glueAt (rootBr' hF hpr) w.1.1 w.2) :=
    (continuous_glueAt₂ (F.flowerParent hF)).comp (continuous_fst.snd.prodMk
      ((continuous_glueAt₂ (rootBr' hF hpr)).comp (continuous_fst.fst.prodMk continuous_snd)))
  have hH : StronglyMeasurable (HT L γ δ p F.toTree off κ (p + 1)) :=
    (continuous_phaseOffT L γ δ F.toTree off κ).stronglyMeasurable.indicator
      (measurableSet_treeTimeDomain _ _ _)
  exact (hH.comp_measurable hg.measurable).integral_prod_right'

theorem TIpat_dRoot_eq_TIgDr {u s : ℝ} (hps : (p : ℝ) < s) (hsu : s < u) (hu : u < p + 1) :
    TIpat L γ δ hF p off κ .dRoot u s = TIgDr L γ δ p hF off κ hpr u s :=
  timeInt_dRoot_eq L γ δ hF p off κ hpr hps hsu hu le_rfl

end Glue

/-! ## Decoration sums with measurable bounded time factors -/

section Core

variable (L γ δ : ℝ) {F : FTree} (hF : F ≠ flower) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
  (k k' : Fin d → ℤ)

theorem norm_epsProd_mul_treeWeight_le (κ : FlowerDecoration F d k k') :
    ‖epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖epsProd F.toTree κ.1.1‖ * |treeWeight L F hF dagger cut1 cut2 κ.1.1| ≤ 1 * 1 :=
        mul_le_mul (norm_epsProd_le _ _) (abs_treeWeight_le_one L hF dagger cut1 cut2 _) (abs_nonneg _)
          zero_le_one
    _ = 1 := one_mul 1

theorem stronglyMeasurable_restP_sumMod (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => restP F (sumMod z.1) κ := by
  have hB : ∀ m, StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => z.1 m :=
    fun m => ((measurable_pi_apply m).comp measurable_fst).stronglyMeasurable
  unfold restP
  exact Finset.stronglyMeasurable_fun_prod _ fun ℓ _ =>
    stronglyMeasurable_zpowSign _ (stronglyMeasurable_sumMod hB _)

/-- A decoration sum whose time factors are measurable in `(t, s)` and bounded by `1`. -/
theorem stronglyMeasurable_decSum {G : FlowerDecoration F d k k' → ℝ × ℝ → ℂ}
    (hGm : ∀ κ, StronglyMeasurable (G κ)) (hG1 : ∀ κ z, ‖G κ z‖ ≤ 1) :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      ∑' κ : FlowerDecoration F d k k', epsProd F.toTree κ.1.1 *
        (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) * G κ z.2 * restP F (sumMod z.1) κ.1.1 := by
  refine stronglyMeasurable_tsum' (fun κ => ?_) fun z => ?_
  · exact ((stronglyMeasurable_const.mul stronglyMeasurable_const).mul
      ((hGm κ).comp_measurable measurable_snd)).mul (stronglyMeasurable_restP_sumMod κ.1.1)
  · refine Summable.of_norm_bounded (summable_restP F (summable_sumMod z.1) k k') fun κ => ?_
    rw [norm_mul, norm_mul]
    calc ‖epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ)‖ * ‖G κ z.2‖ *
          ‖restP F (sumMod z.1) κ.1.1‖ ≤ 1 * 1 * ‖restP F (sumMod z.1) κ.1.1‖ := by
          gcongr
          · exact norm_epsProd_mul_treeWeight_le L hF dagger cut1 cut2 k k' κ
          · exact hG1 κ z.2
      _ = ‖restP F (sumMod z.1) κ.1.1‖ := by ring

end Core

/-! ## The masks -/

section Masks

variable {p : ℕ}

theorem measurableSet_maskPl :
    MeasurableSet {z : ℝ × ℝ | (p : ℝ) < z.2 ∧ z.2 < z.1 ∧ z.1 ≤ p + 1} :=
  (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_fst).inter (measurableSet_le measurable_fst measurable_const))

theorem measurableSet_maskDr :
    MeasurableSet {z : ℝ × ℝ | (p : ℝ) < z.2 ∧ z.2 < z.1 ∧ z.1 < p + 1} :=
  (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_fst).inter (measurableSet_lt measurable_fst measurable_const))

theorem measurableSet_maskPl' :
    MeasurableSet {z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ | (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 ≤ p + 1} :=
  measurable_snd measurableSet_maskPl

theorem measurableSet_maskDr' :
    MeasurableSet {z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ | (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 < p + 1} :=
  measurable_snd measurableSet_maskDr

end Masks

/-! ## One tree, masked, measurable -/

section OneTree

variable (L γ δ : ℝ) (p : ℕ) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k k' : Fin d → ℤ)

theorem stronglyMeasurable_flowerKernelGen_pl (F : FTree) :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 ≤ p + 1 then
        flowerKernelGen L γ δ p F (sumMod z.1) .plain dagger cut1 cut2 z.2.1 z.2.2 k k' else 0 := by
  by_cases hF : F = flower
  · simp only [flowerKernelGen, hF, ↓reduceDIte, ite_self]
    exact stronglyMeasurable_const
  set off : Finset (GBranch (single F.toTree)) := if dagger.isSome then {F.flowerParent hF} else ∅
  set G : FlowerDecoration F d k k' → ℝ × ℝ → ℂ := fun κ z =>
    if (p : ℝ) < z.2 ∧ z.2 < z.1 ∧ z.1 ≤ p + 1 then TIgPl L γ δ p hF off κ.1.1 z.1 z.2 else 0 with hG
  have hGm : ∀ κ, StronglyMeasurable (G κ) := fun κ =>
    StronglyMeasurable.ite measurableSet_maskPl (stronglyMeasurable_TIgPl L γ δ p hF off κ.1.1)
      stronglyMeasurable_const
  have hG1 : ∀ κ z, ‖G κ z‖ ≤ 1 := fun κ z => by
    simp only [hG]
    split_ifs with h
    · rw [← TIpat_plain_eq_TIgPl L γ δ p hF off κ.1.1 h.1 h.2.1 h.2.2]
      exact norm_TIpat_le_one L γ δ hF p off κ.1.1 _ _ _
    · simp
  have heq : (fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 ≤ p + 1 then
        flowerKernelGen L γ δ p F (sumMod z.1) .plain dagger cut1 cut2 z.2.1 z.2.2 k k' else 0) =
      fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 ≤ (p : ℝ) + 1 then
        treePrefactor L γ δ d F.toTree * ∑' κ : FlowerDecoration F d k k', epsProd F.toTree κ.1.1 *
          (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) * G κ z.2 * restP F (sumMod z.1) κ.1.1 else 0 := by
    funext z
    split_ifs with h
    · rw [flowerKernelGen_eq L γ δ hF p]
      congr 1
      refine tsum_congr fun κ => ?_
      have hGκ : G κ z.2 = TIgPl L γ δ p hF off κ.1.1 z.2.1 z.2.2 := by
        simp only [hG]
        exact ite_eq_left_of_eq_true _ _ (eq_true h)
      rw [hGκ, ← TIpat_plain_eq_TIgPl L γ δ p hF off κ.1.1 h.1 h.2.1 h.2.2]
    · rfl
  rw [heq]
  exact StronglyMeasurable.ite measurableSet_maskPl' (stronglyMeasurable_const.mul
    (stronglyMeasurable_decSum L hF dagger cut1 cut2 k k' hGm hG1)) stronglyMeasurable_const

theorem stronglyMeasurable_flowerKernelGen_dr {F : FTree} (hF : F ≠ flower)
    (hpr : (F.flowerParent hF).1.2 ≠ []) :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 < p + 1 then
        flowerKernelGen L γ δ p F (sumMod z.1) .dRoot dagger cut1 cut2 z.2.1 z.2.2 k k' else 0 := by
  set off : Finset (GBranch (single F.toTree)) := if dagger.isSome then {F.flowerParent hF} else ∅
  set G : FlowerDecoration F d k k' → ℝ × ℝ → ℂ := fun κ z =>
    if (p : ℝ) < z.2 ∧ z.2 < z.1 ∧ z.1 < p + 1 then TIgDr L γ δ p hF off κ.1.1 hpr z.1 z.2 else 0 with hG
  have hGm : ∀ κ, StronglyMeasurable (G κ) := fun κ =>
    StronglyMeasurable.ite measurableSet_maskDr (stronglyMeasurable_TIgDr L γ δ p hF off κ.1.1 hpr)
      stronglyMeasurable_const
  have hG1 : ∀ κ z, ‖G κ z‖ ≤ 1 := fun κ z => by
    simp only [hG]
    split_ifs with h
    · rw [← TIpat_dRoot_eq_TIgDr L γ δ p hF off κ.1.1 hpr h.1 h.2.1 h.2.2]
      exact norm_TIpat_le_one L γ δ hF p off κ.1.1 _ _ _
    · simp
  have heq : (fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 < p + 1 then
        flowerKernelGen L γ δ p F (sumMod z.1) .dRoot dagger cut1 cut2 z.2.1 z.2.2 k k' else 0) =
      fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 < (p : ℝ) + 1 then
        treePrefactor L γ δ d F.toTree * ∑' κ : FlowerDecoration F d k k', epsProd F.toTree κ.1.1 *
          (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) * G κ z.2 * restP F (sumMod z.1) κ.1.1 else 0 := by
    funext z
    split_ifs with h
    · rw [flowerKernelGen_eq L γ δ hF p]
      congr 1
      refine tsum_congr fun κ => ?_
      have hGκ : G κ z.2 = TIgDr L γ δ p hF off κ.1.1 hpr z.2.1 z.2.2 := by
        simp only [hG]
        exact ite_eq_left_of_eq_true _ _ (eq_true h)
      rw [hGκ, ← TIpat_dRoot_eq_TIgDr L γ δ p hF off κ.1.1 hpr h.1 h.2.1 h.2.2]
    · rfl
  rw [heq]
  exact StronglyMeasurable.ite measurableSet_maskDr' (stronglyMeasurable_const.mul
    (stronglyMeasurable_decSum L hF dagger cut1 cut2 k k' hGm hG1)) stronglyMeasurable_const

end OneTree

/-! ## The masked kernels of a kind -/

section Masked

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (dagger : Option (Fin 3 → Mom d))
  (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (k k' : Fin d → ℤ)

/-- **The masked plain kernel** `1_{p<s<t≤p+1} 𝒦^{plain}[sumMod b](t, s, k, k')`. -/
noncomputable def Kpl (b : (Fin d → ℤ) → ℂ) (t s : ℝ) : ℂ :=
  if (p : ℝ) < s ∧ s < t ∧ t ≤ p + 1 then
    randFlowerKernel L γ δ p Ntr (sumMod b) kind .plain dagger cut1 cut2 ζ t s k k' else 0

/-- **The masked `dRoot` kernel** `1_{p<s<u<p+1} 𝒦^{dRoot}[sumMod b](u, s, k, k')`. -/
noncomputable def Kdr (b : (Fin d → ℤ) → ℂ) (u s : ℝ) : ℂ :=
  if (p : ℝ) < s ∧ s < u ∧ u < p + 1 then
    randFlowerKernel L γ δ p Ntr (sumMod b) kind .dRoot dagger cut1 cut2 ζ u s k k' else 0

open Classical in
theorem stronglyMeasurable_Kpl :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2 := by
  have heq : (fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2) = fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      ∑ F ∈ (kindTrees Ntr kind).filter (fun F => F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .plain),
        if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 ≤ p + 1 then
          flowerKernelGen L γ δ p F (sumMod z.1) .plain dagger cut1 cut2 z.2.1 z.2.2 k k' else 0 := by
    funext z
    unfold Kpl randFlowerKernel
    split_ifs <;> simp
  rw [heq]
  exact Finset.stronglyMeasurable_fun_sum _ fun F _ =>
    stronglyMeasurable_flowerKernelGen_pl L γ δ p dagger cut1 cut2 k k' F

open Classical in
theorem stronglyMeasurable_Kdr :
    StronglyMeasurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2 := by
  have heq : (fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2) = fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ =>
      ∑ F ∈ (kindTrees Ntr kind).filter (fun F => F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .dRoot),
        if (p : ℝ) < z.2.2 ∧ z.2.2 < z.2.1 ∧ z.2.1 < p + 1 then
          flowerKernelGen L γ δ p F (sumMod z.1) .dRoot dagger cut1 cut2 z.2.1 z.2.2 k k' else 0 := by
    funext z
    unfold Kdr randFlowerKernel
    split_ifs <;> simp
  rw [heq]
  refine Finset.stronglyMeasurable_fun_sum _ fun F hF => ?_
  obtain ⟨-, hF0, hpr⟩ := (Finset.mem_filter.1 hF).2
  exact stronglyMeasurable_flowerKernelGen_dr L γ δ p dagger cut1 cut2 k k' hF0 hpr

theorem Kpl_of_summable {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) {t s : ℝ}
    (h : (p : ℝ) < s ∧ s < t ∧ t ≤ p + 1) :
    Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s =
      randFlowerKernel L γ δ p Ntr b kind .plain dagger cut1 cut2 ζ t s k k' := by
  unfold Kpl
  rw [ite_eq_left_of_eq_true _ _ (eq_true h), sumMod_of_summable hb]

theorem Kdr_of_summable {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) {u s : ℝ}
    (h : (p : ℝ) < s ∧ s < u ∧ u < p + 1) :
    Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b u s =
      randFlowerKernel L γ δ p Ntr b kind .dRoot dagger cut1 cut2 ζ u s k k' := by
  unfold Kdr
  rw [ite_eq_left_of_eq_true _ _ (eq_true h), sumMod_of_summable hb]

/-- **The FTC for the masked kernels.** -/
theorem Kpl_FTC {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) {s : ℝ} (hs : s ∈ Ioo (p : ℝ) (p + 1))
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Ioc s (p + 1)) (ht : t ∈ Ioc s (p + 1)) :
    Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s =
      Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t₀ s +
        ∫ u in t₀..t, Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b u s := by
  rw [Kpl_of_summable L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hb ⟨hs.1, ht.1, ht.2⟩,
    Kpl_of_summable L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hb ⟨hs.1, ht₀.1, ht₀.2⟩,
    randFlowerKernel_plain_sub L γ δ p Ntr hb kind dagger cut1 cut2 ζ hs.1 ht₀.1 ht₀.2 ht.1 ht.2 k k']
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(Set.countable_singleton ((p : ℝ) + 1)).ae_notMem volume] with u hu hmem
  have hu' : u ≠ (p : ℝ) + 1 := hu
  rw [mem_uIoc] at hmem
  have h : (p : ℝ) < s ∧ s < u ∧ u < p + 1 := by
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hs.1, ht₀.1.trans h1, lt_of_le_of_ne (h2.trans ht.2) hu'⟩
    · exact ⟨hs.1, ht.1.trans h1, lt_of_le_of_ne (h2.trans ht₀.2) hu'⟩
  rw [Kdr_of_summable L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hb h]

end Masked

/-! ## Phase covariance -/

section Phase

variable {φ : (Fin d → ℤ) → ℂ}

/-- `χ = \overline{φ(0)} φ`, an additive character for a cubic phase `φ`. -/
noncomputable def phaseChar (φ : (Fin d → ℤ) → ℂ) (m : Fin d → ℤ) : ℂ := (starRingEnd ℂ) (φ 0) * φ m

/-- The phase factor `U = φ(0)^{1−ζ} χ(k − ζ k')`. -/
noncomputable def phaseU (φ : (Fin d → ℤ) → ℂ) (ζ : ℤˣ) (k k' : Fin d → ℤ) : ℂ :=
  φ 0 ^ (1 - (ζ : ℤ)) * phaseChar φ (k - (ζ : ℤ) • k')

theorem mul_conj_phase (hφ : IsCubicPhase φ) (m : Fin d → ℤ) : φ m * (starRingEnd ℂ) (φ m) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ.norm_eq]
  simp

theorem phase_ne_zero (hφ : IsCubicPhase φ) (m : Fin d → ℤ) : φ m ≠ 0 := fun h => by
  have := hφ.norm_eq m
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem phaseChar_add (hφ : IsCubicPhase φ) (a b : Fin d → ℤ) :
    phaseChar φ (a + b) = phaseChar φ a * phaseChar φ b := by
  have h := hφ.rel (a + b) a 0
  rw [show a + b - a + 0 = b by abel] at h
  unfold phaseChar
  rw [← h]
  ring

theorem zpowSign_phase (hφ : IsCubicPhase φ) (ζ : ℤˣ) (m : Fin d → ℤ) :
    zpowSign ζ (φ m) = φ 0 ^ (ζ : ℤ) * phaseChar φ ((ζ : ℤ) • m) := by
  have hu := mul_conj_phase hφ 0
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simp only [zpowSign, ↓reduceIte, Units.val_one, zpow_one, one_smul, phaseChar]
    rw [← mul_assoc, hu, one_mul]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [zpowSign, hne, ↓reduceIte, Units.val_neg, Units.val_one, zpow_neg, zpow_one, neg_smul,
      one_smul, phaseChar]
    have h := hφ.rel 0 m 0
    rw [show (0 : Fin d → ℤ) - m + 0 = -m by abel] at h
    have h1 := mul_conj_phase hφ m
    rw [eq_inv_mul_iff_mul_eq₀ (phase_ne_zero hφ 0)]
    calc φ 0 * (starRingEnd ℂ) (φ m) = (φ m * (starRingEnd ℂ) (φ 0) * φ (-m)) * (starRingEnd ℂ) (φ m) := by
          rw [h]
      _ = (φ m * (starRingEnd ℂ) (φ m)) * ((starRingEnd ℂ) (φ 0) * φ (-m)) := by ring
      _ = (starRingEnd ℂ) (φ 0) * φ (-m) := by rw [h1, one_mul]

theorem prod_zpowSign_phase (hφ : IsCubicPhase φ) {ι : Type*} (s : Finset ι) (ζ : ι → ℤˣ)
    (m : ι → (Fin d → ℤ)) :
    ∏ i ∈ s, zpowSign (ζ i) (φ (m i)) =
      φ 0 ^ (∑ i ∈ s, ((ζ i : ℤˣ) : ℤ)) * phaseChar φ (∑ i ∈ s, ((ζ i : ℤˣ) : ℤ) • m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero, one_mul, phaseChar]
    rw [mul_comm, mul_conj_phase hφ 0]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, zpowSign_phase hφ,
      zpow_add₀ (phase_ne_zero hφ 0), phaseChar_add hφ]
    ring

theorem zpowSign_mul (ζ : ℤˣ) (a b : ℂ) : zpowSign ζ (a * b) = zpowSign ζ a * zpowSign ζ b := by
  unfold zpowSign
  split_ifs <;> simp [map_mul]

/-- `∑_{ℓ≠𝔣} ζ_ℓ = 1 − ζ_𝔣` (the sum rule for the constant labelling `1`). -/
theorem sum_treeSign_erase (F : FTree) :
    ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf, ((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) = 1 - (F.sign : ℤ) := by
  classical
  have h := sum_rule (fun _ : Fin 1 => (1 : ℤˣ)) (fun _ : GNode (single F.toTree) => (1 : ℤ))
    (fun b => by simp) (GNode.root (single F.toTree) 0)
  have hroot : ((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) (GNode.root (single F.toTree) 0).1 : ℤˣ) : ℤ) = 1 := by
    have := treeSign_root F.toTree
    unfold treeSign at this
    rw [this]; rfl
  rw [hroot, one_smul] at h
  have hall : (GNode.root (single F.toTree) 0).leavesBelow = Finset.univ := by
    ext ℓ
    simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨Subsingleton.elim _ _, List.nil_prefix⟩
  rw [hall, ← Finset.add_sum_erase _ _ (Finset.mem_univ F.flowerLeaf)] at h
  have hs := treeSign_flowerLeaf F
  unfold treeSign at hs
  have hs' : ((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) F.flowerLeaf.1 : ℤˣ) : ℤ) = (F.sign : ℤ) :=
    congrArg (fun u : ℤˣ => (u : ℤ)) hs
  simp only [smul_eq_mul, mul_one] at h
  have e : ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf, ((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) =
      ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf, ((nodeSign (fun _ : Fin 1 => (1 : ℤˣ)) ℓ.1 : ℤˣ) : ℤ) := rfl
  rw [e]
  linarith

theorem restP_mul_phase (hφ : IsCubicPhase φ) (F : FTree) {k k' : Fin d → ℤ} (κ : FlowerDecoration F d k k')
    (b : (Fin d → ℤ) → ℂ) :
    restP F (fun m => φ m * b m) κ.1.1 = phaseU φ F.sign k k' * restP F b κ.1.1 := by
  unfold restP
  simp only [zpowSign_mul, Finset.prod_mul_distrib]
  congr 1
  have hp := prod_zpowSign_phase hφ (Finset.univ.erase F.flowerLeaf) (fun ℓ => treeSign F.toTree ℓ.toNode)
    (fun ℓ => κ.1.1 ℓ.toNode)
  rw [hp, sum_treeSign_erase]
  have hmom := flowerDecoration_root κ
  have e : ∑ ℓ ∈ Finset.univ.erase F.flowerLeaf, ((treeSign F.toTree ℓ.toNode : ℤˣ) : ℤ) • κ.1.1 ℓ.toNode =
      k - (F.sign : ℤ) • k' := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hmom.symm
  rw [e]
  rfl

theorem norm_phaseU (hφ : IsCubicPhase φ) (ζ : ℤˣ) (k k' : Fin d → ℤ) : ‖phaseU φ ζ k k'‖ = 1 := by
  unfold phaseU phaseChar
  rw [norm_mul, norm_zpow, hφ.norm_eq, one_zpow, norm_mul, Complex.norm_conj, hφ.norm_eq, hφ.norm_eq]
  norm_num

variable (L γ δ : ℝ) (p : ℕ)

theorem flowerKernelGen_mul_phase (hφ : IsCubicPhase φ) (F : FTree) (b : (Fin d → ℤ) → ℂ) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F (fun m => φ m * b m) pat dagger cut1 cut2 t s k k' =
      phaseU φ F.sign k k' * flowerKernelGen L γ δ p F b pat dagger cut1 cut2 t s k k' := by
  by_cases hF : F = flower
  · simp [flowerKernelGen, hF]
  rw [flowerKernelGen_eq L γ δ hF p, flowerKernelGen_eq L γ δ hF p]
  have h : ∀ κ : FlowerDecoration F d k k', epsProd F.toTree κ.1.1 *
      (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) *
        TIpat L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ.1.1 pat t s *
          restP F (fun m => φ m * b m) κ.1.1 =
      phaseU φ F.sign k k' * (epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) *
        TIpat L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ.1.1 pat t s *
          restP F b κ.1.1) := fun κ => by
    rw [restP_mul_phase hφ F κ b]
    ring
  rw [tsum_congr h, tsum_mul_left]
  ring

open Classical in
theorem randFlowerKernel_mul_phase (hφ : IsCubicPhase φ) (Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (kind : FlowerKind)
    (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ)
    (k k' : Fin d → ℤ) :
    randFlowerKernel L γ δ p Ntr (fun m => φ m * b m) kind pat dagger cut1 cut2 ζ t s k k' =
      phaseU φ ζ k k' * randFlowerKernel L γ δ p Ntr b kind pat dagger cut1 cut2 ζ t s k k' := by
  unfold randFlowerKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [flowerKernelGen_mul_phase L γ δ p hφ, (Finset.mem_filter.1 hF).2.1]

theorem sumMod_mul_phase (hφ : IsCubicPhase φ) (b : (Fin d → ℤ) → ℂ) :
    sumMod (fun m => φ m * b m) = fun m => φ m * sumMod b m := by
  unfold sumMod
  by_cases hb : Summable fun m => ‖b m‖
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((summable_mul_phase hφ).2 hb)),
      ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (summable_mul_phase hφ).1 hb)),
      ite_eq_right_of_eq_false _ _ (eq_false hb)]
    funext m
    simp

variable (Ntr : ℕ) (kind : FlowerKind) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
  (k k' : Fin d → ℤ)

theorem Kpl_mul_phase (hφ : IsCubicPhase φ) (b : (Fin d → ℤ) → ℂ) (t s : ℝ) :
    Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' (fun m => φ m * b m) t s =
      phaseU φ ζ k k' * Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s := by
  unfold Kpl
  rw [sumMod_mul_phase hφ, randFlowerKernel_mul_phase L γ δ p hφ]
  split_ifs <;> simp

theorem Kdr_mul_phase (hφ : IsCubicPhase φ) (b : (Fin d → ℤ) → ℂ) (u s : ℝ) :
    Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' (fun m => φ m * b m) u s =
      phaseU φ ζ k k' * Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b u s := by
  unfold Kdr
  rw [sumMod_mul_phase hφ, randFlowerKernel_mul_phase L γ δ p hφ]
  split_ifs <;> simp

theorem enorm_Kpl_mul_phase (hφ : IsCubicPhase φ) (b : (Fin d → ℤ) → ℂ) (t s : ℝ) :
    ‖Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' (fun m => φ m * b m) t s‖ₑ =
      ‖Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s‖ₑ := by
  rw [Kpl_mul_phase L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hφ, enorm_mul,
    ← ofReal_norm (phaseU φ ζ k k'), norm_phaseU hφ, ENNReal.ofReal_one, one_mul]

theorem enorm_Kdr_mul_phase (hφ : IsCubicPhase φ) (b : (Fin d → ℤ) → ℂ) (u s : ℝ) :
    ‖Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' (fun m => φ m * b m) u s‖ₑ =
      ‖Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b u s‖ₑ := by
  rw [Kdr_mul_phase L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hφ, enorm_mul,
    ← ofReal_norm (phaseU φ ζ k k'), norm_phaseU hφ, ENNReal.ofReal_one, one_mul]

end Phase

/-! ## The pieces, masked -/

section Pieces

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (k k' : Fin d → ℤ)

/-- The largest leaf count of the trees of a kind. -/
noncomputable def leafMax (Ntr : ℕ) (kind : FlowerKind) : ℕ :=
  (kindTrees Ntr kind).sup fun F => Fintype.card (GLeaf (single F.toTree))

theorem card_le_leafMax {F : FTree} (hF : F ∈ kindTrees Ntr kind) :
    Fintype.card (GLeaf (single F.toTree)) ≤ leafMax Ntr kind := by
  unfold leafMax
  exact Finset.le_sup (f := fun F : FTree => Fintype.card (GLeaf (single F.toTree))) hF

theorem hasSum_Kpl_cut1 (hL : 0 < L) (dagger : Option (Fin 3 → Mom d)) (cut2 : Option ℕ)
    (b : (Fin d → ℤ) → ℂ) (t s : ℝ) :
    HasSum (fun j => Kpl L γ δ p Ntr kind dagger (some j) cut2 ζ k k' b t s)
      (Kpl L γ δ p Ntr kind dagger none cut2 ζ k k' b t s) := by
  by_cases h : (p : ℝ) < s ∧ s < t ∧ t ≤ p + 1
  · simp only [Kpl, ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact hasSum_randFlowerKernel_cut1 L γ δ hL p (summable_sumMod b) Ntr kind .plain dagger ζ cut2 t s k k'
  · simp only [Kpl, ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact hasSum_zero

theorem hasSum_Kpl_cut2 (hL : 0 < L) (dagger : Option (Fin 3 → Mom d)) (cut1 : Option ℕ)
    (b : (Fin d → ℤ) → ℂ) (t s : ℝ) :
    HasSum (fun j => Kpl L γ δ p Ntr kind dagger cut1 (some j) ζ k k' b t s)
      (Kpl L γ δ p Ntr kind dagger cut1 none ζ k k' b t s) := by
  by_cases h : (p : ℝ) < s ∧ s < t ∧ t ≤ p + 1
  · simp only [Kpl, ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact hasSum_randFlowerKernel_cut2 L γ δ hL p (summable_sumMod b) Ntr kind .plain dagger ζ cut1 t s k k'
  · simp only [Kpl, ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact hasSum_zero

theorem hasSum_Kpl_dagger (hd : 0 < d) (hL : L ≠ 0) (cut1 cut2 : Option ℕ) (b : (Fin d → ℤ) → ℂ) (t s : ℝ) :
    HasSum (fun x : DagIdx d => dagPhase L γ δ ζ x k' s *
        Kpl L γ δ p Ntr kind (some (dagLabel L x)) cut1 cut2 ζ k k' b t s)
      (Kpl L γ δ p Ntr kind none cut1 cut2 ζ k k' b t s) := by
  by_cases h : (p : ℝ) < s ∧ s < t ∧ t ≤ p + 1
  · simp only [Kpl, ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact hasSum_randFlowerKernel_dagger L γ δ p (summable_sumMod b) Ntr kind .plain cut1 cut2 ζ hd hL t s k k'
  · simp only [Kpl, ite_eq_right_of_eq_false _ _ (eq_false h), mul_zero]
    exact hasSum_zero

open Classical in
/-- **The `†` support**: the term of `x` vanishes if some label `w_m`, `m ≠ i`, has `|w_m/L| ≥ ℓ_max M₁`. -/
theorem Kpl_dagger_eq_zero (hd : 0 < d) (hL : 0 < L) (cut2 : Option ℕ) (j : ℕ) (b : (Fin d → ℤ) → ℂ)
    (t s : ℝ) (x : DagIdx d)
    (hx : ∃ m, m ≠ x.1 ∧ (leafMax Ntr kind : ℝ) * (2 ^ j * L) ≤ ‖latticePoint L (x.2.1 m)‖) :
    Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j) cut2 ζ k k' b t s = 0 := by
  unfold Kpl randFlowerKernel
  split_ifs
  · refine Finset.sum_eq_zero fun F hF => ?_
    obtain ⟨m, hm, hle⟩ := hx
    have hc : (Fintype.card (GLeaf (single F.toTree)) : ℝ) ≤ leafMax Ntr kind := by
      exact_mod_cast card_le_leafMax Ntr kind (Finset.mem_filter.1 hF).1
    have h2 : (0 : ℝ) ≤ 2 ^ j * L := by positivity
    exact flowerKernelGen_dagger_eq_zero L γ δ p hd hL (sumMod b) .plain cut2 j t s x
      ⟨m, hm, le_trans (mul_le_mul_of_nonneg_right hc h2) hle⟩
  · rfl

/-- `B₀ = 2 ℓ_max M₁` for the kind. -/
noncomputable def kerB0K (j₁ : ℕ) : ℝ := 2 * (leafMax Ntr kind : ℝ) * (2 ^ j₁ * L)

/-- `R = 8B₀ + 4B₀² + M₂ + 1` for the kind. -/
noncomputable def kerRK (j₁ j₂ : ℕ) : ℝ :=
  8 * kerB0K L Ntr kind j₁ + 4 * kerB0K L Ntr kind j₁ ^ 2 + 2 ^ j₂ * L + 1

open Classical in
/-- **The shift identity** (`X3-KerInv`) for the masked kernel of a kind. -/
theorem Kpl_shift (hL : 0 < L) (c : Fin 3 → Mom d) (j₁ j₂ : ℕ) (b : (Fin d → ℤ) → ℂ) (t s : ℝ)
    {D : Fin d → ℤ} {M : ℝ}
    (hk : kerRK L Ntr kind j₁ j₂ ≤ ‖latticePoint L k‖) (hkD : kerRK L Ntr kind j₁ j₂ ≤ ‖latticePoint L (k + D)‖)
    (hM1 : 2 * kerB0K L Ntr kind j₁ ≤ M) (hM2 : 2 ^ j₂ * L + 4 * kerB0K L Ntr kind j₁ ^ 2 ≤ 2 * M)
    (hrep : ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
      (|ipL L k z| ≤ M ↔ |ipL L (k + D) z| ≤ M) ∧ (|ipL L k z| ≤ M → ipL L k z = ipL L (k + D) z)) :
    Kpl L γ δ p Ntr kind (some c) (some j₁) (some j₂) ζ (k + D) (k' + (ζ : ℤ) • D) b t s =
      Kpl L γ δ p Ntr kind (some c) (some j₁) (some j₂) ζ k k' b t s := by
  unfold Kpl randFlowerKernel
  split_ifs
  · refine Finset.sum_congr rfl fun F hF => ?_
    have hFs : F.sign = ζ := (Finset.mem_filter.1 hF).2.1
    have hc : (Fintype.card (GLeaf (single F.toTree)) : ℝ) ≤ leafMax Ntr kind := by
      exact_mod_cast card_le_leafMax Ntr kind (Finset.mem_filter.1 hF).1
    have h2 : (0 : ℝ) ≤ 2 ^ j₁ * L := by positivity
    have hB : kerB0 L F j₁ ≤ kerB0K L Ntr kind j₁ := by
      unfold kerB0 kerB0K
      have := mul_le_mul_of_nonneg_right hc h2
      linarith
    have hB0 : 0 ≤ kerB0 L F j₁ := by unfold kerB0; positivity
    have hB2 := pow_le_pow_left₀ hB0 hB 2
    have hR : kerR L F j₁ j₂ ≤ kerRK L Ntr kind j₁ j₂ := by
      unfold kerR kerRK
      linarith
    rw [← hFs]
    exact flowerKernelGen_shift_eq L γ δ p hL (sumMod b) .plain c j₁ j₂ t s (hR.trans hk) (hR.trans hkD)
      (by linarith) (by linarith) hrep
  · rfl

end Pieces

end WaveTurbulence.Fixedpt
