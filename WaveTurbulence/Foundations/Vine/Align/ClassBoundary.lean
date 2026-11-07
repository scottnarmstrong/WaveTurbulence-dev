/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.ClassShape
public import WaveTurbulence.Foundations.Vine.Align.ClassRoute
/-! Common boundary and route fields for every genuine class member. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssembly hM σ)))
  (hy : y ∈ classU (unitsSplit (alignedAssembly hM σ)) p kind
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)))

/-- The complete `hmom` function is the representative's function. -/
theorem classShape_hmom :
    (classShape hM σ D hS layer hLayer hp y hy).hmom (class_disj hM σ D hS layer hLayer hp y hy) =
      (stShape hM σ).hmom (unitBlk_disj hM σ) :=
  commonShape_hmom hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- The complete `hclk` function is the representative's function. -/
theorem classShape_hclk :
    (classShape hM σ D hS layer hLayer hp y hy).hclk (class_disj hM σ D hS layer hLayer hp y hy) =
      (stShape hM σ).hclk (unitBlk_disj hM σ) :=
  commonShape_hclk hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- The route of every class member is the same literal common-garden route. -/
theorem classShape_route (hG : (stSt S σ).G.IsPlain) :
    (classShape hM σ D hS layer hLayer hp y hy).route y.1.plain hG = (stShape hM σ).route hS hG :=
  commonShape_route hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1 hG

end WaveTurbulence.VineAlign
