/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.OrderedSourceMass
public import WaveTurbulence.Foundations.Sumint.GroupedProductIntegral

/-!
# The exact independent masses controlling the source input integral

The actual static-domain mass is reduced to local pair and normal
integrals with every interval retained. Pair masses still depend on the
distinguished times; the oscillatory window bounds are uniform in those
times and can therefore be inserted before the last linear integration.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The exact local pair mass, retaining the first-pair ordering strip when required. -/
@[expose] noncomputable def orderedPairMass {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ≥0∞ :=
  ∫⁻ z in Icc (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a)))
    (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))),
      ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t u a z)

/-- The exact local normal mass in its three original input intervals. -/
@[expose] noncomputable def normalFactorMass {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}) : ℝ≥0∞ :=
  ∫⁻ z in Icc (fun j => lo (.inr (.inr ⟨i,j⟩)))
    (fun j => hi (.inr (.inr ⟨i,j⟩))), ENNReal.ofReal ‖normalTimeSum D L γ δ p ν r t i z‖

/-- Exact nonnegative product form of the grouped ordered source norm. -/
theorem ofReal_groupedOrderedSourceNorm {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (z : GroupedTimes D.S) :
    ENNReal.ofReal (groupedOrderedSourceNorm D L γ δ η p ν r t z) =
      (∏ i : Fin D.S.I, ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i (z.1 i)‖) *
      (∏ a : Σ i : Fin D.S.I, Fin (D.S.m i),
        ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t z.1 a (z.2.1 a))) *
      (∏ i : {i : Fin D.S.I // D.S.nor i = true}, ENNReal.ofReal ‖normalTimeSum D L γ δ p ν r t i (z.2.2 i)‖) := by
  have hF : 0 ≤ ∏ i : Fin D.S.I, ‖linearTimeSum D L γ δ p ν r t i (z.1 i)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hG : 0 ≤ ∏ a : Σ i : Fin D.S.I, Fin (D.S.m i), orderedPairNorm D L γ δ η p ν r t z.1 a (z.2.1 a) :=
    Finset.prod_nonneg (fun a _ => orderedPairNorm_nonneg D L γ δ η p ν r t z.1 a (z.2.1 a))
  unfold groupedOrderedSourceNorm
  rw [ENNReal.ofReal_mul (mul_nonneg hF hG),ENNReal.ofReal_mul hF,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ENNReal.ofReal_prod_of_nonneg (fun a _ => orderedPairNorm_nonneg D L γ δ η p ν r t z.1 a _),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]

/-- TARGET sumint Step 2: actual source input mass controlled by the independent oscillatory masses. -/
theorem lintegral_static_box_cutoffPhaseSum_le_factor_masses {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) :
    (∫⁻ τ in Icc lo hi ∩ staticTimeDomain D, ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) ≤
      ∫⁻ u in linearFamilyBox D.S lo hi,
        (∏ i : Fin D.S.I, ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i (u i)‖) *
        (∏ a : Σ i : Fin D.S.I, Fin (D.S.m i), orderedPairMass D L γ δ η p ν r t lo hi u a) *
        (∏ i : {i : Fin D.S.I // D.S.nor i = true}, normalFactorMass D L γ δ p ν r t lo hi i) := by
  apply (lintegral_static_box_cutoffPhaseSum_le_grouped D hD hL δ p ν r t lo hi).trans_eq
  simp_rw [ofReal_groupedOrderedSourceNorm]
  let F : Fin D.S.I → ℝ → ℝ≥0∞ :=
    fun i s => ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i s‖
  let G : (Fin D.S.I → ℝ) → (Σ i : Fin D.S.I, Fin (D.S.m i)) → (ℝ × ℝ) → ℝ≥0∞ :=
    fun u a z => ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t u a z)
  let H : {i : Fin D.S.I // D.S.nor i = true} → (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun i z => ENNReal.ofReal ‖normalTimeSum D L γ δ p ν r t i z‖
  have hG (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Measurable (G u a) :=
    ENNReal.measurable_ofReal.comp ((measurable_orderedPairNorm D hL γ δ η p ν r t a).comp
      ((measurable_const (a := u)).prodMk measurable_id))
  have hH (i : {i : Fin D.S.I // D.S.nor i = true}) : Measurable (H i) :=
    ENNReal.measurable_ofReal.comp (measurable_normalTimeSum_norm D hL γ δ p ν r t i)
  have he := lintegral_grouped_product_eq D.S lo hi F G H hG hH
  exact he

end WaveTurbulence.Sumint
