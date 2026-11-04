/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockTraceDerivative
public import WaveTurbulence.Foundations.ClassJR.MCProd

/-! # Simultaneous frozen-energy trace estimate

The dimension r enters only through derivatives j≤r charged to the
codimension, never as a factor raised to the surviving derivative order k.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- Smooth tensor-valued fiber in the r frozen coordinates. -/
theorem contDiff_tensor_blockInsert {r : ℕ} {κ Γ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : κ → ℝ) :
    ContDiff ℝ ∞ (fun a : Fin r → ℝ => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (Sum.elim a β))) := by
  have hp : ContDiff ℝ ∞ (fun a : Fin r → ℝ => toLp 1 (Sum.elim a β)) := by
    simp_rw [sumBlocks_toLp_eq]
    exact (((sumLeftZeroL1 (ι := Fin r) (κ := κ)).toContinuousLinearMap.contDiff).comp
      (toL1 r).contDiff).add contDiff_const
  exact ((contDiff_lift1 hs).iteratedFDeriv_right (by exact_mod_cast le_top)).comp hp

/-- Pointwise trace bound with the precise codimension-dependent loss. -/
theorem dnorm_blockTraceSymbol_le_cube {r : ℕ} {κ Γ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : κ → ℝ) :
    dnorm k (blockTraceSymbol C) β lam ≤ (2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        ∫⁻ a : Fin r → ℝ, dnorm (k+j) C (Sum.elim a β) lam := by
  apply (dnorm_blockTraceSymbol_le hs k β).trans
  have hh := enorm_le_sum_lintegral_iteratedFDeriv r
    (fun a : Fin r → ℝ => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (Sum.elim a β)))
      (contDiff_tensor_blockInsert hs k β) 0
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro j _
  exact (lintegral_mono (fun a => enorm_tensor_frozenBlock_derivative_le hs k j β a)).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

/-- Product-volume compatibility for the literal block insertion. -/
theorem lintegral_sumElim {ι κ : Type} [Fintype ι] [Fintype κ]
    {H : (ι ⊕ κ → ℝ) → ℝ≥0∞}
    (hH : Measurable (fun p : (ι → ℝ) × (κ → ℝ) => H (Sum.elim p.1 p.2))) :
    (∫⁻ α : ι ⊕ κ → ℝ, H α) = ∫⁻ a : ι → ℝ, ∫⁻ β : κ → ℝ, H (Sum.elim a β) := by
  have hh := lintegral_sum_iter (H := fun a β => H (Sum.elim a β)) hH
  have he (α : ι ⊕ κ → ℝ) : Sum.elim (fun i => α (.inl i)) (fun i => α (.inr i)) = α := by
    funext i
    cases i <;> rfl
  simpa only [he] using hh

/-- Fully integrated simultaneous trace. Every additional r^j loss has j≤r. -/
theorem lintegral_dnorm_blockTraceSymbol_le {r : ℕ} {κ Γ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) :
    (∫⁻ β : κ → ℝ, dnorm k (blockTraceSymbol C) β lam) ≤ (2:ℝ≥0∞)^r *
      ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
        ∫⁻ α : Fin r ⊕ κ → ℝ, dnorm (k+j) C α lam := by
  have hp : Continuous (fun p : (Fin r → ℝ) × (κ → ℝ) => Sum.elim p.1 p.2) := by
    apply continuous_pi
    intro i
    cases i with
    | inl i => simpa only [Sum.elim_inl] using
        (show Continuous (fun p : (Fin r → ℝ) × (κ → ℝ) => p.1 i) from by fun_prop)
    | inr i => simpa only [Sum.elim_inr] using
        (show Continuous (fun p : (Fin r → ℝ) × (κ → ℝ) => p.2 i) from by fun_prop)
  have hm (j : ℕ) : Measurable (fun p : (Fin r → ℝ) × (κ → ℝ) =>
      dnorm (k+j) C (Sum.elim p.1 p.2) lam) := (continuous_dnorm hs (k+j)).measurable.comp hp.measurable
  have hf (j : ℕ) : Measurable (fun β : κ → ℝ => ENNReal.ofReal ((r:ℝ)^j)*
      ∫⁻ a : Fin r → ℝ, dnorm (k+j) C (Sum.elim a β) lam) :=
    measurable_const.mul (hm j).lintegral_prod_left'
  calc
    _ ≤ ∫⁻ β : κ → ℝ, (2:ℝ≥0∞)^r * ∑ j ∈ Finset.range (r+1), ENNReal.ofReal ((r:ℝ)^j)*
      ∫⁻ a : Fin r → ℝ, dnorm (k+j) C (Sum.elim a β) lam :=
        lintegral_mono (dnorm_blockTraceSymbol_le_cube hs k)
    _ = (2:ℝ≥0∞)^r * ∑ j ∈ Finset.range (r+1),
      ∫⁻ β : κ → ℝ, ENNReal.ofReal ((r:ℝ)^j)*
        ∫⁻ a : Fin r → ℝ, dnorm (k+j) C (Sum.elim a β) lam := by
      rw [lintegral_const_mul' _ _ (by finiteness),lintegral_finsetSum (f := fun j β => ENNReal.ofReal ((r:ℝ)^j)*∫⁻ a : Fin r → ℝ,
        dnorm (k+j) C (Sum.elim a β) lam) _ (fun j _ => hf j)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      calc
        _ = ∫⁻ a : Fin r → ℝ, ∫⁻ β : κ → ℝ, dnorm (k+j) C (Sum.elim a β) lam :=
          (lintegral_lintegral_swap (hm j).aemeasurable).symm
        _ = _ := (lintegral_sumElim (H := fun α => dnorm (k+j) C α lam) (hm j)).symm

end WaveTurbulence.RegAsymp
