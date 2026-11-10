/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.PhaseContinuity
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

end WaveTurbulence.RegRed
