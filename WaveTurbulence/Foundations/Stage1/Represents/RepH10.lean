/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH9

/-!
# S2 REPRESENTS, VINE-D (10): the total absolute mass of the expansion with vine factors is finite

`tsum_constWH_le`: the masses of the assembled modes are those of the slot modes times the vine masses `Π_j Mh j`
(uniform in the centres).  `sum_lintegral_gIH_ne_top`: `Σ_{ξh} Σ_κ ∫⁻ ‖gIH‖ < ∞` (Fubini for `value_eqH`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

namespace AsmCtxH
variable (A : AsmCtxH S d)

theorem Mh_nonneg (j : A.J) (c : Fin 4 → Fin d → ℤ) : 0 ≤ A.Mh j :=
  le_trans (tsum_nonneg fun l => A.H.w_nn j c l) (A.hMh j c)

theorem lintegral_gIH_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    ∫⁻ τ, ‖A.gIH ξh κ τ‖ₑ ≤ ENNReal.ofReal (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) := by
  classical
  set c : ℝ := ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ with hc
  calc ∫⁻ τ, ‖A.gIH ξh κ τ‖ₑ
      ≤ ∫⁻ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun _ => ENNReal.ofReal c) τ := by
        refine lintegral_mono fun τ => ?_
        have := A.norm_gIH_le ξh κ τ
        by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
        · simp only [Set.indicator_of_mem hτ] at this ⊢
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        · simp only [Set.indicator_of_notMem hτ] at this ⊢
          have h0 : A.gIH ξh κ τ = 0 := norm_le_zero_iff.1 this
          rw [h0]; simp
    _ = ENNReal.ofReal c * volume (splicedTimeDomain S A.layer0 A.tt) :=
        lintegral_indicator_const (measurableSet_splicedTimeDomain S A.layer0 A.tt) _
    _ ≤ ENNReal.ofReal c * 1 := by
        gcongr; exact volume_splicedTimeDomain_le _ _ _
    _ = _ := mul_one _

theorem tsum_constWH_le :
    ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ ≤
      (∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖) *
        ∏ j, ENNReal.ofReal (A.Mh j) := by
  classical
  have hcnt : ∀ s, Countable (A.fam.Λ s) := A.fam.cnt
  have hsig := ENNReal.tsum_sigma' (β := fun ξ : XiT A.fam => ∀ j, A.H.Λ j (hingeCen A.fam A.hS A.hmom ξ j))
    (fun ξh => ENNReal.ofReal ‖A.constWH ξh‖)
  refine (le_of_eq hsig).trans ?_
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ξ => ?_
  have e1 : ∀ ζ : (∀ j, A.H.Λ j (hingeCen A.fam A.hS A.hmom ξ j)), ENNReal.ofReal ‖A.constWH ⟨ξ, ζ⟩‖ =
      ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ *
        ENNReal.ofReal (∏ j, A.H.w j _ (ζ j)) := by
    intro ζ
    rw [A.norm_constWH, ENNReal.ofReal_mul (norm_nonneg _)]
  simp_rw [e1]
  rw [ENNReal.tsum_mul_left]
  gcongr
  rw [tsum_ofReal_prod_fintype (fun j l => A.H.w j (hingeCen A.fam A.hS A.hmom ξ j) l)
    (fun j l => A.H.w_nn j _ l)]
  refine Finset.prod_le_prod' fun j _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (A.H.w_nn j _) (A.H.w_sum j _)]
  exact ENNReal.ofReal_le_ofReal (A.hMh j _)

open scoped Classical in
theorem sum_lintegral_gIH_ne_top :
    ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gIH ξh κ τ‖ₑ ≠ ⊤ := by
  set N : ℝ≥0∞ := ((((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) : ℕ) : ℝ≥0∞) with hN
  have h1 : ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gIH ξh κ τ‖ₑ ≤
      ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ * N := by
    refine ENNReal.tsum_le_tsum fun ξh => ?_
    calc ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gIH ξh κ τ‖ₑ
        ≤ ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.constWH ξh‖ * ENNReal.ofReal ‖A.E ξh.1 κ‖ := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          refine (A.lintegral_gIH_le ξh κ).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
      _ = ENNReal.ofReal ‖A.constWH ξh‖ * ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξh.1 κ‖ :=
          ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact A.toAsmCtx.tsum_bondProd_le ξh.1
  refine ne_top_of_le_ne_top ?_ h1
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ A.tsum_constWH_le) (by simp [hN])
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ A.toAsmCtx.tsum_constW_le)
    (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top A.toAsmCtx.mass_ne_top (by simp))

end AsmCtxH
end WaveTurbulence.Represents
