/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubiniInputs

/-! # The per-state factorized form of `K^U` as an `sSum` (V5 Step 4b, step 4)

`clLocalKernel_eq_sSum`: `K^U = sSum RS (n0 = b, n1 = b.child kept) Φ` with `Φ(t, E, F) = K^T(t, t₁, t₂; E, F, g, h)`,
the form of TARGET (tildeJ2) for one state (hypotheses: `L ≠ 0`, `HF`, the input summability).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

include hS hT hi hU in
/-- **The kernel of `U = S ∪ T` is the S-side sum with the lower factor `K^T`.** -/
theorem clLocalKernel_eq_sSum (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    clLocalKernel D hG RU L γ δ F layer hLayer base t0 t1 t2 e f g h =
      sSum RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) :=
  clLocalKernel_split_KT hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL hF

end WaveTurbulence.VineEstS4
