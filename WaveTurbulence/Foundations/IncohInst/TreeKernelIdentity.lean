/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeSummandIdentity
public import WaveTurbulence.Foundations.IncohInst.GardenSign
public import WaveTurbulence.Foundations.IncohInst.SourceOrders
public import WaveTurbulence.Foundations.Incoh.RawSourceTimeFubini
public import WaveTurbulence.Foundations.Incoh.RawTreeAgreement

/-! # The literal B1 tree kernel equals the analytic raw source kernel -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- Conditional exact original-kernel identity. Summability is discharged independently from
the source spatial input norms; it is used solely for the lattice/time Fubini step. -/
theorem KTstar_eq_raw_of_summable {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (k : Mom d) (ts : Fin 2 → ℝ)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctions LG F) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    KTstar L γ δ F LG (ts 0) (ts 1) k =
      (treeCarrier hX).sourceTreeKernel (gardenCircle LG.garden) C.rootCoordinates
        L γ δ (treeLayerLinks LG hX) (actualTreeFibers (d := d) LG hX C).timeDomain (treeInputFunctions LG F) ts k := by
  let I := (actualTreeFibers (d := d) LG hX C).timeDomain ∩ C.rootCoordinates.causalRootCut ts
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (treeLayerLinks (d := d) LG hX j)) :=
    Set.inter_subset_left.trans (actualTreeFibers (d := d) LG hX C).timeDomain_subset_linkBoxes
  unfold KTstar kernelK
  rw [tree_order_eq_twice_links hX]
  rw [← (treeLatticeEquiv hX d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length) * LG.garden.zeta *
    (∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      (epsDec LG.garden (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => ts 0) (ts 1)) (ts 1)
          (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode)
          (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ)) = _
  simp_rw [tree_summand_eq_linkIntegral hX C L γ δ F k ts]
  unfold MomentumTreeData.sourceTreeKernel MomentumTreeData.sourceIntegral
  rw [(treeCarrier hX).integral_sourceTimeIntegrand_eq_tsum (gardenCircle LG.garden) L γ δ
    (treeLayerLinks LG hX) I hbox (treeInputFunctions LG F) k hs]
  rw [Complex.ofReal_pow]
  unfold coupling
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [gardenCircle_coe]
  ring

end WaveTurbulence.IncohInst
