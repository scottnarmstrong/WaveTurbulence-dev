/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelIntegrand
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Absolute time / decoration exchange for the literal source kernel -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory Finset Set

theorem integral_freeTimeBox {w : ℕ} (LG : LayeredGarden w) :
    (∫ τ, (LGSpine.freeTimeBox LG).indicator (fun _ => (1 : ℝ)) τ) = 1 := by
  have hm : MeasurableSet (LGSpine.freeTimeBox LG) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  change (∫ τ, (LGSpine.freeTimeBox LG).indicator (1 : (LG.garden.FreeBranch → ℝ) → ℝ) τ) = 1
  rw [integral_indicator_one hm]
  have hv : (volume : Measure (LG.garden.FreeBranch → ℝ)) (LGSpine.freeTimeBox LG) = 1 := by
    rw [LGSpine.freeTimeBox,volume_pi_pi]
    simp only [Real.volume_Icc,add_sub_cancel_left,ENNReal.ofReal_one,prod_const_one]
  rw [Measure.real,hv,ENNReal.toReal_one]

theorem integral_norm_kernelIntegrand_le {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelIntegrand L γ δ F LG up s k₀ κ τ‖) ≤ LGSpine.inputLeafMajorant L F LG k₀ κ := by
  have h := integral_mono (integrable_kernelIntegrand L γ δ F LG up s k₀ κ).norm
    ((LGSpine.integrable_freeTimeBox LG).const_mul (LGSpine.inputLeafMajorant L F LG k₀ κ))
    (norm_kernelIntegrand_le L γ δ F LG up s k₀ κ)
  rw [integral_const_mul,integral_freeTimeBox,mul_one] at h
  exact h

theorem kernelK_eq_integral_tsum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    kernelK L γ δ F LG up s k₀ nroot nfl =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∫ τ, ∑' κ : GenDecoration LG.garden d nroot nfl, kernelIntegrand L γ δ F LG up s k₀ κ τ := by
  have hmajor := LGSpine.summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF
  have hsum : Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelIntegrand L γ δ F LG up s k₀ κ τ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_kernelIntegrand_le L γ δ F LG up s k₀) hmajor
  let : Countable (GenDecoration LG.garden d nroot nfl) := by
    unfold GenDecoration
    infer_instance
  have hx := integral_tsum_of_summable_integral_norm
    (integrable_kernelIntegrand L γ δ F LG up s k₀) hsum
  unfold kernelK
  simp_rw [← integral_kernelIntegrand]
  rw [hx]

theorem lone_count_le_one_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain) (j : Fin w) :
    (univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 := by
  have he : (univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ) = ∅ := by
    ext ℓ
    constructor
    · intro hℓ
      have hl : G.IsLone ℓ := (Finset.mem_filter.mp hℓ).2.2
      have hn := hG ℓ
      change G.mark ℓ = some .lower at hl
      rw [hl] at hn
      contradiction
    · intro hℓ
      exact (Finset.notMem_empty ℓ hℓ).elim
  rw [he,Finset.card_empty]
  exact Nat.zero_le _

/-- TARGET defkg0 with the absolutely convergent lattice sum moved inside the
actual time integral. Ordinary-garden typing supplies the lone-leaf bound. -/
theorem KG_eq_integral_tsum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : LG.garden.IsPlain) (top : ℝ)
    (nroot : Fin w → (Fin d → ℤ))
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (latticePoint L n)|) :
    KG L γ δ F LG top nroot =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∫ τ, ∑' κ : GenDecoration LG.garden d nroot 0,
          kernelIntegrand L γ δ F LG (fun _ => top) 0 0 κ τ := by
  apply kernelK_eq_integral_tsum L γ δ F LG (fun _ => top) 0 0 nroot 0
    (lone_count_le_one_of_plain LG.garden hG)
  intro ℓ hℓ
  simpa only [zero_add] using hF ℓ hℓ

end WaveTurbulence.RegRed
