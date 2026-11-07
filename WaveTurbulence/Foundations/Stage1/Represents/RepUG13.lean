/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG12
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG10
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G2 in the shape of `exists_hinge_data_units_leaf_w`

`g2_units`: the hypothesis `G2` of `exists_hinge_data_units_leaf_w` for the units of `stSt S σ` (centre
`centre j c = sumintBoundary ζ_j (latPt ∘ c)`, selection = non-vanishing literal gap indicator): every selected decoration whose
hinge momenta lie in the unit balls of `c` has `sumintBoundary` of them in `outSet (unitD …)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 VineParamContract

open scoped Classical in
theorem g2_units (P : WTParams) {w : ℕ} {S : Garden w} (hM : S.molecule.IsMolecule) (hS : S.IsPlain)
    (σ : Prescription S) (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ))
    (D : SplicedKernelData (stSt S σ).G P.d) (hD : D.gapSpecification = gapSpecification S σ)
    {n₀ : Fin (unitBlocks S σ).length → ℕ}
    {B₀ : ∀ j, CLChainAssembly S (regionOf (unitBlk hM σ j)) (n₀ j)} (hM9 : VINEPARAM)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    ∀ κ : GenDecoration (stSt S σ).G P.d roots 0,
      splicedGapIndicator (stSt S σ).G D P.L P.γ P.η base κ.1 ≠ 0 →
      ∀ j (c : Fin 4 → Fin P.d → ℤ),
        (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (S.sign (unitBlk hM σ j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) ∈
          outSet (unitD hM9 (B₀ j) RD hG layer hLayer
            (sumintBoundary (S.sign (unitBlk hM σ j).upper.toNode) (fun i => latPt P.d (c i))) base) P.L P.γ P.η :=
  fun κ hκ j c hball =>
    mem_outSet_of_gsb hM hS σ hL P.γ P.η base roots κ D hD hκ j c hball _ rfl rfl

end WaveTurbulence.Represents
