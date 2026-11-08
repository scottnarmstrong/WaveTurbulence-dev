/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.WeightOp
public import WaveTurbulence.Foundations.Flower.V5WB.K.Defs

/-! # V5W-B-WORLD: the weighted member kernel of a state (V5-SPACE-EXT's `memberB` with `bWN`, every selector) -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B

variable {w d : ℕ} {ι : Type*}

/-- The weighted member kernel of a state at a region (selected rows, masked normalized bond weight). -/
def memberB (κ : KPar d) (lam : ℝ) (ψ : WD d) (X : FamilyReconstruction w ι)
    (c : ChainAt X.skeleton X.family) : ℂ :=
  memberMX X.data X.plain (clRegionData X.skeleton c.block c.cl) κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam (bWN ψ κ X c.U) κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h

end WaveTurbulence.Flower.V5WB
