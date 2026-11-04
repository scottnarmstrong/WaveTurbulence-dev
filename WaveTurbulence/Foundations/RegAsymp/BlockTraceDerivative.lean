/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.BlockInsertion

/-! # Simultaneous energy traces without a dimension loss in derivative order -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- Freeze the left block of energy variables, retaining the right block. -/
def blockTraceSymbol {ι κ Γ : Type} (C : (ι ⊕ κ → ℝ) → Γ → ℂ)
    (β : κ → ℝ) (lam : Γ) : ℂ := C (Sum.elim 0 β) lam

/-- The surviving derivative variables still enter by an ℓ¹ isometry. -/
theorem dnorm_blockTraceSymbol_le {ι κ Γ : Type} [Fintype ι] [Fintype κ]
    {C : (ι ⊕ κ → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : κ → ℝ) :
    dnorm k (blockTraceSymbol C) β lam ≤ dnorm k C (Sum.elim 0 β) lam := by
  let i := (sumRightZeroL1 (ι := ι) (κ := κ)).toContinuousLinearMap
  have hi : ‖i‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp [i])
  have hF := contDiff_lift1 hs
  have he : lift1 (blockTraceSymbol C) lam = lift1 C lam ∘ i := rfl
  unfold dnorm
  rw [he,i.iteratedFDeriv_comp_right hF (toLp 1 β) (by exact_mod_cast le_top),← ofReal_norm,← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (lift1 C lam) (i (toLp 1 β))‖*∏ _a : Fin k, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hi)) (norm_nonneg _)
    _ = _ := by simp only [Finset.prod_const_one,mul_one]; rfl

/-- Inserting r frozen sup-norm coordinates into the full ℓ¹ space. -/
def frozenBlockL1 {r : ℕ} {κ : Type} [Fintype κ] : (Fin r → ℝ) →L[ℝ] L1 (Fin r ⊕ κ) :=
  (sumLeftZeroL1 (ι := Fin r) (κ := κ)).toContinuousLinearMap.comp (toL1 r)

theorem norm_frozenBlockL1_le {r : ℕ} {κ : Type} [Fintype κ] :
    ‖(frozenBlockL1 (r := r) (κ := κ))‖ ≤ (r:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro α
  change ‖sumLeftZeroL1 (toL1 r α)‖ ≤ (r:ℝ)*‖α‖
  rw [LinearIsometry.norm_map]
  exact ((toL1 r).le_opNorm α).trans (mul_le_mul_of_nonneg_right (norm_toL1_le_card r) (norm_nonneg _))

/-- Only the number j of frozen-coordinate derivatives carries r^j;
the surviving derivative order k incurs no dimensional loss. -/
theorem enorm_tensor_frozenBlock_derivative_le {r : ℕ} {κ Γ : Type} [Fintype κ]
    {C : (Fin r ⊕ κ → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k j : ℕ) (β : κ → ℝ) (α : Fin r → ℝ) :
    ‖iteratedFDeriv ℝ j (fun a : Fin r → ℝ =>
        iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (Sum.elim a β))) α‖ₑ ≤
      ENNReal.ofReal ((r:ℝ)^j)*dnorm (k+j) C (Sum.elim α β) lam := by
  let P := (frozenBlockL1 (r := r) (κ := κ))
  let b := sumRightZeroL1 (ι := Fin r) (toLp 1 β)
  let Φ := iteratedFDeriv ℝ k (lift1 C lam)
  have hΦ : ContDiff ℝ ∞ Φ := (contDiff_lift1 hs).iteratedFDeriv_right (by exact_mod_cast le_top)
  have hT : ContDiff ℝ ∞ (fun x => Φ (x+b)) := hΦ.comp (contDiff_id.add contDiff_const)
  have he : (fun a : Fin r → ℝ => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (Sum.elim a β))) =
      (fun x => Φ (x+b)) ∘ P := by
    funext a
    simp only [Function.comp_apply,Φ,b,P,frozenBlockL1,ContinuousLinearMap.comp_apply,toL1_apply,
      sumBlocks_toLp_eq]
    rfl
  rw [he,P.iteratedFDeriv_comp_right hT α (by exact_mod_cast le_top),iteratedFDeriv_comp_add_right,
    ← ofReal_norm,dnorm,← ofReal_norm,← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  dsimp only [Φ]
  rw [norm_iteratedFDeriv_iteratedFDeriv]
  have hx : P α+b = toLp 1 (Sum.elim α β) := (sumBlocks_toLp_eq α β).symm
  rw [hx,mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_frozenBlockL1_le (r := r) (κ := κ)) j) (norm_nonneg _)

end WaveTurbulence.RegAsymp
