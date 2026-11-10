/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowConservation

/-! # Integer branching conservation reconstructed from the M9 fiber -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- No integrality or inverse-matrix premise is hidden: the integer source
conservation follows by an injective lattice embedding and the proved
physical reconstruction. -/
theorem clRebuildInteger_conservation
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) :
    ∀ v ∈ U, clRebuildLabels R k.1 β v.toNode =
      clRebuildLabels R k.1 β (v.child 0)-clRebuildLabels R k.1 β (v.child 1)+
        clRebuildLabels R k.1 β (v.child 2) := by
  let f := latticePointAddHom (d := d) 1
  have hf : Function.Injective f := latticePoint_injective_of_ne_zero one_ne_zero
  clear_value f
  let β' : Fin 4 → Mom d := fun j => f (β j)
  have hβ' : (((G.sign a.toNode : ℤ) : ℝ) • (β' 0-β' 1)) = β' 2-β' 3 := by
    change (((G.sign a.toNode : ℤ) : ℝ) • (f (β 0)-f (β 1))) = f (β 2)-f (β 3)
    rw [Int.cast_smul_eq_zsmul,← map_sub,← map_zsmul,hβ,map_sub]
  let k' : FlowFiber G.molecule U a b (Mom d) (β' 2-β' 3) :=
    ⟨fun e => f (k.1 e),
      by rw [← map_flow,k.2.1,map_neg,map_sub],
      by rw [← map_flow,k.2.2.1,map_sub],
      by intro v hv ha hb; rw [← map_flow,k.2.2.2 v hv ha hb,map_zero]⟩
  have hk' : k'.1 = fun e => f (k.1 e) := rfl
  clear_value k'
  have hcons := clRebuildLabels_conservation hU R β' hβ' k'
  have hmap (x : GNode G.tree) : f (clRebuildLabels R k.1 β x) = clRebuildLabels R k'.1 β' x := by
    rw [hk']
    exact clRebuildLabels_map R f k.1 β x
  intro v hv
  apply hf
  calc
    _ = clRebuildLabels R k'.1 β' v.toNode := hmap _
    _ = _ := hcons v hv
    _ = _ := by rw [map_add,map_sub,hmap,hmap,hmap]

end WaveTurbulence.VineEstS2
