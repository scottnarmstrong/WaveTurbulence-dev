/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeKernelIdentity
public import WaveTurbulence.Foundations.Incoh.TreeSourceAbsoluteConvergence

/-! # The original tree kernel identity with every Fubini premise discharged -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- Literal B1 `KTstar` equals the analytic causal tree source from source input norms alone. -/
theorem KTstar_eq_raw {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (C : TreeClockSelection hX)
    {d : ℕ} (hd : 0 < d) (L γ δ : ℝ) (hL : 1 ≤ L) (F : ℕ → Mom d → ℝ)
    {p : ℕ} (hp : ∀ a, LG.layer a ≤ p) {B : ℝ}
    (hF : ∀ r ≤ p, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B)
    (k : Mom d) (ts : Fin 2 → ℝ) :
    KTstar L γ δ F LG (ts 0) (ts 1) k =
      (treeCarrier hX).sourceTreeKernel (gardenCircle LG.garden) C.rootCoordinates
        L γ δ (treeLayerLinks LG hX) (actualTreeFibers (d := d) LG hX C).timeDomain
        (treeInputFunctions LG F) ts k := by
  apply KTstar_eq_raw_of_summable hX C L γ δ F k ts
  exact (treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice hd
    (treeInputFunctions LG F) hL (by omega) (by omega)
    (fun a => treeInputFunctions_spatialNorm_le LG F hp hF a) k

end WaveTurbulence.IncohInst
