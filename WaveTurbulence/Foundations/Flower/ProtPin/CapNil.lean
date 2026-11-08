/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapFinal

/-! # D3 PROT-PIN: a protected object with the empty chain has no branches

With `X = nil` (allowed by `ProtCfg.Valid trace`) the protected tree is its lone leaf and the cap couple is a pair
of leaves: there are no branches, so every configuration's designation is the empty one (`capc_fix_nil`) and the
kernel is that of `none`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

theorem capc_noBranch {w p : ℕ} {LG : LayeredGarden w} (hsh : ProtShape p .nil LG) (b : GBranch LG.garden.tree) :
    False := by
  have h := b.2
  match w, LG, hsh, b, h with
  | 1, LG, hsh, b, h =>
    rw [show b.1.1 = 0 from Subsingleton.elim _ _, hsh.2.1.1] at h
    exact MainCoef.not_mem_branching_leaf _ h
  | 2, LG, hsh, b, h =>
    obtain ⟨LG1, Dc⟩ := CapData.exists_of_decodes hsh.2.1
    by_cases h0 : b.1.1 = 0
    · rw [h0, Dc.tree0] at h
      exact MainCoef.not_mem_branching_leaf _ h
    · rw [Dc.idx _ h0, Dc.tree1] at h
      exact MainCoef.not_mem_branching_leaf _ h
  | 0, _, hsh, _, _ => exact hsh.elim
  | _ + 3, _, hsh, _, _ => exact hsh.elim

/-- **With the empty chain every designation is empty.** -/
theorem capc_fix_nil {w p : ℕ} {LG : LayeredGarden w} (hsh : ProtShape p .nil LG) (cfg : ProtCfg) (s t up : ℝ) :
    (cfg.fix .nil s t up : GBranch LG.garden.tree → Option ℝ) = ProtCfg.none.fix .nil s t up := by
  funext b
  exact (capc_noBranch hsh b).elim

theorem capc_box_nil (t p q' : ℝ) : ProtCfg.trace.box .nil t p q' = ProtCfg.none.box .nil t p q' := rfl

end WaveTurbulence.Flower.ProtPin
