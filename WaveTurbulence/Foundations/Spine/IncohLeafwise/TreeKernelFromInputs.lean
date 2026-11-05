/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeKernelIdentity
public import WaveTurbulence.Foundations.Incoh.TreeSourceAbsoluteConvergence

/-! # The original tree kernel identity with every Fubini premise discharged -/

public section
noncomputable section
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links
open WaveTurbulence.LGSpine

/-- Literal B1 `KTstar` equals the analytic causal tree source from source input norms alone. -/
theorem treeLeaves_eq_rawL {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (C : TreeClockSelection hX)
    {d : ℕ} (hd : 0 < d) (L γ δ : ℝ) (hL : 1 ≤ L) (H : LeafProfiles 1 d)
    {p : ℕ} (_hp : ∀ a, LG.layer a ≤ p) {B : ℝ}
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B)
    (k : Mom d) (ts : Fin 2 → ℝ) :
    treeLeaves L γ δ LG H (ts 0) (ts 1) k =
      (treeCarrier hX).sourceTreeKernel (gardenCircle LG.garden) C.rootCoordinates
        L γ δ (treeLayerLinks LG hX) (actualTreeFibers (d := d) LG hX C).timeDomain
        (treeInputFunctionsL LG H) ts k := by
  apply treeLeaves_eq_raw_of_summableL hX C L γ δ H k ts
  exact (treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice hd
    (treeInputFunctionsL LG H) hL (by omega) (by omega)
    (fun a => treeInputFunctions_spatialNorm_leL hX H hH a) k

end WaveTurbulence.IncohLeafwise
