/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2Det

/-!
# X3 Part2Op: from the kernel bound to the operator bound

**Statement.**
1. (`Xker_eq_rand`, `Yker_eq_rand`, `Wker_eq_rand`) For `p < s < t ≤ p + 1`, the kernels of `𝒳 − 1`, `𝒴`, `𝒲`
   (`Flower-Kernel.lean`) are the kernels of the kinds `X`, `Y`, `W` with the plain pattern, no `†` and no
   cutoffs (`randFlowerKernel`). The maps `rootOf`, `bottomOf` are injective, so the image sums are the
   index sums.
2. (`ZNorm_kernelOp_le_of_event`) Let `b` be summable data in the Part 2 events of both `ζ`, and let
   `A ≥ Λ + d + 1`. Then `‖𝒦 c‖_Z ≤ 2 · 2^{Λ/2} B S_L ‖c‖_Z` for any `c ∈ Z^Λ`, where `S_L = latSum d L`. This
   holds for each kernel `𝒦` that agrees with the kind's kernel on `p < s < t ≤ p + 1`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree
open scoped ENNReal

variable {d : ℕ}

/-! ## The kernels of `𝒳`, `𝒴`, `𝒲` -/

theorem rootOf_injective : Function.Injective rootOf := by
  rintro ⟨i, F, T₁, T₂⟩ ⟨i', F', T₁', T₂'⟩ h
  simp only [rootOf, FTree.node.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem bottomOf_injective : Function.Injective bottomOf := fun x y h => by
  rw [← bottom_bottomOf x, ← bottom_bottomOf y, h]

section Ident

variable (L γ δ : ℝ) (p N : ℕ) (aP : (Fin d → ℤ) → ℂ) (ζ : ℤˣ) {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
  (ht : t ≤ p + 1) (k k' : Fin d → ℤ)

include hps hst ht in
open Classical in
theorem Xker_eq_rand :
    Xker L γ δ p N aP ζ t s k k' = randFlowerKernel L γ δ p N aP .X .plain none none none ζ t s k k' := by
  unfold Xker randFlowerKernel
  have hfilt : (kindTrees N .X).filter (fun F => F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .plain) =
      (Xset N).filter (fun F => F.sign = ζ) := by
    show (Xset N).filter _ = _
    refine Finset.filter_congr fun F hF => ?_
    have hF0 : F ≠ flower := (Finset.mem_filter.1 hF).2
    exact ⟨fun h => h.1, fun h => ⟨h, hF0, trivial⟩⟩
  rw [hfilt]
  exact Finset.sum_congr rfl fun F _ => (X2Probes.flowerKernelGen_plain L γ δ p F aP hps hst ht k k').symm

include hps hst ht in
open Classical in
theorem Yker_eq_rand :
    Yker L γ δ p N aP ζ t s k k' = randFlowerKernel L γ δ p N aP .Y .plain none none none ζ t s k k' := by
  unfold Yker randFlowerKernel
  show _ = ∑ F ∈ ((Yind N).image rootOf).filter _, _
  rw [Finset.filter_image, Finset.sum_image (fun x _ y _ h => rootOf_injective h)]
  have hfilt : (Yind N).filter (fun x => (rootOf x).sign = ζ ∧
      ∃ hF : rootOf x ≠ flower, treePatValid (rootOf x) hF .plain) =
      (Yind N).filter (fun x => (rootOf x).sign = ζ) := by
    refine Finset.filter_congr fun x _ => ?_
    have hF0 : rootOf x ≠ flower := by simp [rootOf]
    exact ⟨fun h => h.1, fun h => ⟨h, hF0, trivial⟩⟩
  rw [hfilt]
  exact Finset.sum_congr rfl fun x _ => (X2Probes.flowerKernelGen_plain L γ δ p _ aP hps hst ht k k').symm

include hps hst ht in
open Classical in
theorem Wker_eq_rand :
    Wker L γ δ p N aP ζ t s k k' = randFlowerKernel L γ δ p N aP .W .plain none none none ζ t s k k' := by
  unfold Wker randFlowerKernel
  show _ = ∑ F ∈ ((Wind N).image bottomOf).filter _, _
  rw [Finset.filter_image, Finset.sum_image (fun x _ y _ h => bottomOf_injective h)]
  have hfilt : (Wind N).filter (fun x => (bottomOf x).sign = ζ ∧
      ∃ hF : bottomOf x ≠ flower, treePatValid (bottomOf x) hF .plain) =
      (Wind N).filter (fun x => (bottomOf x).sign = ζ) := by
    refine Finset.filter_congr fun x _ => ?_
    have hF0 : bottomOf x ≠ flower := graft_ne_flower (by simp)
    exact ⟨fun h => h.1, fun h => ⟨h, hF0, trivial⟩⟩
  rw [hfilt]
  exact Finset.sum_congr rfl fun x _ => (X2Probes.flowerKernelGen_plain L γ δ p _ aP hps hst ht k k').symm

end Ident

/-! ## The operator bound -/

section Op

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (π : P2Par)

/-- **The operator bound on the event.** -/
theorem ZNorm_kernelOp_le_of_event (hπ : π.Valid) (hL : 1 ≤ L) (hd : 0 < d) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hA : Λ + (d + 1) ≤ π.A) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (hev : ∀ ζ, b ∈ part2Event L γ δ p Ntr kind ζ π)
    {K : ℤˣ → ℝ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℂ}
    (hK : ∀ ζ t s k k', (p : ℝ) < s → s < t → t ≤ p + 1 →
      K ζ t s k k' = randFlowerKernel L γ δ p Ntr b kind .plain none none none ζ t s k k')
    {c : ArrI p d} (hc : c ∈ ZSpace L Λ p) :
    ZNorm L Λ (kernelOp p K c) ≤ ENNReal.ofReal (2 * 2 ^ (Λ / 2) * π.B * latSum d L) * ZNorm L Λ c := by
  have hB := hπ.hB
  -- on `(p, t)`, the kernel is the masked one
  have heq : ∀ ζ (t : Icc (p : ℝ) (p + 1)) k k', ∀ s ∈ Ioo (p : ℝ) t,
      K ζ t s k k' = Kpl L γ δ p Ntr kind none none none ζ k k' b t s := fun ζ t k k' s hs => by
    rw [hK ζ t s k k' hs.1 hs.2 t.2.2,
      Kpl_of_summable L γ δ p Ntr kind none none none ζ k k' hb ⟨hs.1, hs.2, t.2.2⟩]
  have hlin : ∀ ζ (t : Icc (p : ℝ) (p + 1)) k k',
      ∫⁻ s in Ioo (p : ℝ) t, ‖K ζ t s k k'‖ₑ ≤ ENNReal.ofReal (π.B * wtm L ζ π.A k k') := by
    intro ζ t k k'
    rw [setLIntegral_congr_fun measurableSet_Ioo fun s hs => by rw [heq ζ t k k' s hs]]
    exact lintegral_Kpl_le L γ δ p Ntr kind ζ π hπ hL hd hb (hev ζ) t.2 k k'
  have haesm : ∀ ζ (t : Icc (p : ℝ) (p + 1)) k k',
      AEStronglyMeasurable (fun s => ‖K ζ t s k k'‖) (volume.restrict (Ioo (p : ℝ) t)) := by
    intro ζ t k k'
    refine (measurable_Kpl_slice L γ δ p Ntr kind ζ none none none k k' b t).norm.aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => congrArg norm (heq ζ t k k' s hs).symm)
  have hInt : ∀ ζ (t : Icc (p : ℝ) (p + 1)) k k', IntegrableOn (fun s => ‖K ζ t s k k'‖) (Ioo (p : ℝ) t) := by
    intro ζ t k k'
    refine ⟨haesm ζ t k k', ?_⟩
    show ∫⁻ s in Ioo (p : ℝ) t, ‖‖K ζ t s k k'‖‖ₑ < ⊤
    simp only [enorm_norm]
    exact (hlin ζ t k k').trans_lt ENNReal.ofReal_lt_top
  have hKint : ∀ (ζ : ℤˣ) (t : Icc (p : ℝ) (p + 1)) k k',
      IntervalIntegrable (fun s => ‖K ζ t s k k'‖) volume p t := fun ζ t k k' =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le t.2.1).2 (hInt ζ t k k')
  have hKb : ∀ (ζ : ℤˣ) (t : Icc (p : ℝ) (p + 1)) k k',
      ∫ s in (p : ℝ)..t, ‖K ζ t s k k'‖ ≤
        π.B * jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-π.A) := by
    intro ζ t k k'
    rw [intervalIntegral.integral_of_le t.2.1, integral_Ioc_eq_integral_Ioo,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => norm_nonneg _) (haesm ζ t k k')]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hB (wtm_nonneg _ _ _ _ _)) ?_
    simp only [ofReal_norm]
    exact hlin ζ t k k'
  have hpt := fun t k => norm_kernelOp_le hL hΛ hA hB hc hKint hKb t k
  have hZ : ZNorm L Λ (kernelOp p K c) ≤
      ENNReal.ofReal (2 * (2 ^ (Λ / 2) * π.B * latSum d L * (ZNorm L Λ c).toReal)) :=
    ZNorm_le_of_wt L (fun t n => (hpt t n).trans (le_of_eq (mul_comm _ _)))
  refine hZ.trans (le_of_eq ?_)
  have hS : 0 ≤ latSum d L := tsum_nonneg fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  rw [show 2 * (2 ^ (Λ / 2) * π.B * latSum d L * (ZNorm L Λ c).toReal) =
      (2 * 2 ^ (Λ / 2) * π.B * latSum d L) * (ZNorm L Λ c).toReal by ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hc.2.ne]

end Op

end WaveTurbulence.Fixedpt
