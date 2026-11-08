/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # D2a PROT-KER: sanity lemmas (probe section 8, copied by source, see COPIED-SHA256SUMS) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtDefs

theorem protCfg_none_fix (X : RegChain) (s t up : ℝ) {w : ℕ} {T : Fin w → TTree} (b : GBranch T) :
    ProtCfg.none.fix X s t up b = none := by
  unfold ProtCfg.fix ProtCfg.pins
  split_ifs <;> rfl

theorem filtWeight_empty {w d : ℕ} {G : Garden w} (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (k : GNode G.tree → Mom d) : filtWeight (∅ : Finset (GBranch G.tree)) ann M k = 1 := by
  simp [filtWeight]

theorem filtWeight_norm_le {w d : ℕ} {G : Garden w} (F : Finset (GBranch G.tree))
    (M : GBranch G.tree → ℝ) (k : GNode G.tree → Mom d) (h0 : ∀ u, |chi0 u| ≤ 1) :
    ‖filtWeight F (fun _ => false) M k‖ ≤ 1 := by
  unfold filtWeight
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro b _
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
  exact h0 _

end WaveTurbulence.Flower.ProtDefs
