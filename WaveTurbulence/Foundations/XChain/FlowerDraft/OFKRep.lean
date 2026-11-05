/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKFubini

/-!
# O-FK, part 5: regrouping by the flower mode; the kernel representation

`fOp_kernel_rep'`: `𝒥_F[b] = 𝒦_{𝒥̃_F} b` (obligation O-FK), with its integrability and summability side conditions.
The decorations of `F.toTree` are regrouped by `κ_𝔣 = k'`, and the sum over the decorations with `κ_𝔣 = k'`
commutes with the integral over the flower-parent time.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

section Flower

variable {F : FTree}

/-! ### One flower mode `k'` -/

instance (F : FTree) (d : ℕ) (k k' : Fin d → ℤ) : Countable (FlowerDecoration F d k k') :=
  inferInstanceAs (Countable {κ : TreeDecoration F.toTree d k // κ.1 F.flowerLeaf.toNode = k'})

theorem summable_leafBound_fiber (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) (k k' : Fin d → ℤ) :
    Summable fun κ : FlowerDecoration F d k k' =>
      leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ.1.1 :=
  (summable_leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) k).comp_injective
    (Subtype.val_injective : Function.Injective fun κ : FlowerDecoration F d k k' => κ.1)

theorem summable_norm_flowerSummand_fiber (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) (t : ℝ) (k k' : Fin d → ℤ) (s : ℝ) :
    Summable fun κ : FlowerDecoration F d k k' => ‖flowerSummand L γ δ p F hF aP b t κ.1.1 s‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_flowerSummand_le L γ δ hF p haP hb t κ.1.1 s)
    ((summable_leafBound_fiber p haP hb k k').mul_left _)

theorem flowerKernel_mul_inFac (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ} {b : ArrI p d}
    (t s : ℝ) (k k' : Fin d → ℤ) :
    flowerKernel L γ δ p F aP t s k k' * inFac F b s k' =
      treePrefactor L γ δ d F.toTree *
        ∑' κ : FlowerDecoration F d k k', flowerSummand L γ δ p F hF aP b t κ.1.1 s := by
  rw [flowerKernel_eq L γ δ hF, mul_assoc, ← tsum_mul_right]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold flowerSummand
  rw [κ.2]

theorem integral_flowerKernel_fiber (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) {t : ℝ} (ht : (p : ℝ) ≤ t) (k k' : Fin d → ℤ) :
    ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' * inFac F b s k' =
      treePrefactor L γ δ d F.toTree *
        ∑' κ : FlowerDecoration F d k k', ∫ s in (p : ℝ)..t, flowerSummand L γ δ p F hF aP b t κ.1.1 s := by
  rw [intervalIntegral.integral_congr fun s _ => flowerKernel_mul_inFac L γ δ hF p (b := b) t s k k',
    intervalIntegral.integral_const_mul]
  refine congrArg (treePrefactor L γ δ d F.toTree * ·) ?_
  have hint : ∀ κ : FlowerDecoration F d k k',
      IntegrableOn (fun s => flowerSummand L γ δ p F hF aP b t κ.1.1 s) (Ioc (p : ℝ) t) := fun κ =>
    integrableOn_flowerSummand L γ δ hF p haP hb t κ.1.1
  have hsum : Summable fun κ : FlowerDecoration F d k k' =>
      ∫ s in Ioc (p : ℝ) t, ‖flowerSummand L γ δ p F hF aP b t κ.1.1 s‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun κ => ?_)
      (((summable_leafBound_fiber p haP hb k k').mul_left (boxVolW p F hF t)).mul_left
        (volume.real (Ioc (p : ℝ) t)))
    calc ∫ s in Ioc (p : ℝ) t, ‖flowerSummand L γ δ p F hF aP b t κ.1.1 s‖
        ≤ ∫ _ in Ioc (p : ℝ) t,
            boxVolW p F hF t * leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ.1.1 :=
          setIntegral_mono_on (hint κ).norm
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
            fun s _ => norm_flowerSummand_le L γ δ hF p haP hb t κ.1.1 s
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [intervalIntegral.integral_of_le ht]
  calc ∫ s in Ioc (p : ℝ) t, ∑' κ : FlowerDecoration F d k k', flowerSummand L γ δ p F hF aP b t κ.1.1 s
      = ∑' κ : FlowerDecoration F d k k', ∫ s in Ioc (p : ℝ) t, flowerSummand L γ δ p F hF aP b t κ.1.1 s :=
        key.symm
    _ = _ := tsum_congr fun κ => (intervalIntegral.integral_of_le ht).symm

theorem intervalIntegrable_flowerKernel (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) {t : ℝ} (ht : (p : ℝ) ≤ t) (k k' : Fin d → ℤ) :
    IntervalIntegrable (fun s => flowerKernel L γ δ p F aP t s k k' * inFac F b s k') volume p t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  have hfun : (fun s => flowerKernel L γ δ p F aP t s k k' * inFac F b s k') = fun s =>
      treePrefactor L γ δ d F.toTree *
        ∑' κ : FlowerDecoration F d k k', flowerSummand L γ δ p F hF aP b t κ.1.1 s :=
    funext fun s => flowerKernel_mul_inFac L γ δ hF p t s k k'
  rw [hfun]
  have hmeas : StronglyMeasurable fun s => ∑' κ : FlowerDecoration F d k k',
      flowerSummand L γ δ p F hF aP b t κ.1.1 s :=
    stronglyMeasurable_tsum (f := fun (κ : FlowerDecoration F d k k') s =>
        flowerSummand L γ δ p F hF aP b t κ.1.1 s)
      (fun κ => stronglyMeasurable_flowerSummand L γ δ hF p hb t κ.1.1)
      fun s => (summable_norm_flowerSummand_fiber L γ δ hF p haP hb t k k' s).of_norm
  set M := ‖treePrefactor L γ δ d F.toTree‖ * ∑' κ : FlowerDecoration F d k k',
    boxVolW p F hF t * leafBound F.toTree (flowerData F (LeafIn.ofGood hb) haP) κ.1.1
  refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
    (stronglyMeasurable_const.mul hmeas).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (norm_tsum_le_tsum_norm (summable_norm_flowerSummand_fiber L γ δ hF p haP hb t k k' s)).trans
    ((summable_norm_flowerSummand_fiber L γ δ hF p haP hb t k k' s).tsum_le_tsum
      (fun κ => norm_flowerSummand_le L γ δ hF p haP hb t κ.1.1 s)
      ((summable_leafBound_fiber p haP hb k k').mul_left _))

/-! ### Assembly -/

/-- **O-FK: the kernel representation of `𝒥_F[b]`.** -/
theorem fOp_kernel_rep' (hF : F ≠ flower) (p : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) (t : Icc (p : ℝ) (p + 1)) (k : Fin d → ℤ) :
    (∀ k', IntervalIntegrable (fun s => flowerKernel L γ δ p F aP t s k k' * inFac F b s k') volume p t) ∧
    Summable (fun k' => ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' * inFac F b s k') ∧
    fOp L γ δ p aP F b t k = ∑' k', ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' * inFac F b s k' := by
  have ht : (p : ℝ) ≤ t := t.2.1
  set D := flowerData F (LeafIn.ofGood hb) haP
  set P := treePrefactor L γ δ d F.toTree
  let I : TreeDecoration F.toTree d k → ℂ := fun κ =>
    ∫ s in (p : ℝ)..t, flowerSummand L γ δ p F hF aP b t κ.1 s
  have hI : ∀ κ, I κ = epsProd F.toTree κ.1 * timeIntG L γ δ F.toTree κ.1 D p t := fun κ =>
    integral_flowerSummand L γ δ hF p haP hb ht κ.1
  have hIs : Summable I :=
    Summable.of_norm_bounded ((summable_leafBound F.toTree D k).mul_left (boxVol F.toTree p t))
      fun κ => by rw [hI]; exact norm_treeSummandG_le L γ δ p F.toTree D t k κ
  let e : (Σ k', FlowerDecoration F d k k') ≃ TreeDecoration F.toTree d k :=
    Equiv.sigmaFiberEquiv (fun κ : TreeDecoration F.toTree d k => κ.1 F.flowerLeaf.toNode)
  have hIsig : Summable fun x : (Σ k', FlowerDecoration F d k k') => I (e x) := e.summable_iff.2 hIs
  have hfib : ∀ k', ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' * inFac F b s k' =
      P * ∑' κ : FlowerDecoration F d k k', I κ.1 := fun k' =>
    integral_flowerKernel_fiber L γ δ hF p haP hb ht k k'
  refine ⟨fun k' => intervalIntegrable_flowerKernel L γ δ hF p haP hb ht k k', ?_, ?_⟩
  · simp only [hfib]
    exact hIsig.sigma.mul_left P
  · rw [fOp_eq_treeTermG L γ δ p haP hb F t k]
    simp only [hfib]
    show P * ∑' κ : TreeDecoration F.toTree d k, epsProd F.toTree κ.1 * timeIntG L γ δ F.toTree κ.1 D p t = _
    rw [tsum_mul_left]
    congr 1
    calc ∑' κ : TreeDecoration F.toTree d k, epsProd F.toTree κ.1 * timeIntG L γ δ F.toTree κ.1 D p t
        = ∑' κ, I κ := tsum_congr fun κ => (hI κ).symm
      _ = ∑' x, I (e x) := (e.tsum_eq I).symm
      _ = ∑' k', ∑' κ : FlowerDecoration F d k k', I κ.1 := hIsig.tsum_sigma

end Flower

end WaveTurbulence.SysAPI
