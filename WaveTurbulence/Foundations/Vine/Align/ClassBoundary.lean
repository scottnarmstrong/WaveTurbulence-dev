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

section ClassBoundaryMk
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssemblyMk hM σ Mk)))
  (hy : y ∈ classU (unitsSplit (alignedAssemblyMk hM σ Mk)) p kind
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)))
  {mkY : Set (CLVine y.1.skeleton)} (hT : MemberMarked p kind hM σ D hS layer hLayer y mkY)

include hp hy

/-- B1b-3 (Mk-general form of `classShape_hmom`).
The complete `hmom` function is the representative's function. -/
theorem classShape_hmomMk :
    (classShapeMk hM σ D hS layer hLayer hp y hy hT).hmom (class_disjMk hM σ D hS layer hLayer hp y hy) =
      (stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) :=
  commonShape_hmomMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1
    (hT _ (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2)

/-- B1b-3 (Mk-general form of `classShape_hclk`).
The complete `hclk` function is the representative's function. -/
theorem classShape_hclkMk :
    (classShapeMk hM σ D hS layer hLayer hp y hy hT).hclk (class_disjMk hM σ D hS layer hLayer hp y hy) =
      (stShape hM σ Mk).hclk (unitBlkMk_disj hM σ Mk) :=
  commonShape_hclkMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1
    (hT _ (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2)

/-- B1b-3 (Mk-general form of `classShape_route`).
The route of every class member is the same literal common-garden route. -/
theorem classShape_routeMk (hG : (stSt S σ Mk).G.IsPlain) :
    (classShapeMk hM σ D hS layer hLayer hp y hy hT).route y.1.plain hG = (stShape hM σ Mk).route hS hG :=
  commonShape_routeMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1
    (hT _ (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2) hG

end ClassBoundaryMk

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
  classShape_hmomMk hM σ D hS layer hLayer hp y hy (memberMarked_empty p kind hM σ D hS layer hLayer y)

/-- The complete `hclk` function is the representative's function. -/
theorem classShape_hclk :
    (classShape hM σ D hS layer hLayer hp y hy).hclk (class_disj hM σ D hS layer hLayer hp y hy) =
      (stShape hM σ).hclk (unitBlk_disj hM σ) :=
  classShape_hclkMk hM σ D hS layer hLayer hp y hy (memberMarked_empty p kind hM σ D hS layer hLayer y)

/-- The route of every class member is the same literal common-garden route. -/
theorem classShape_route (hG : (stSt S σ).G.IsPlain) :
    (classShape hM σ D hS layer hLayer hp y hy).route y.1.plain hG = (stShape hM σ).route hS hG :=
  classShape_routeMk hM σ D hS layer hLayer hp y hy (memberMarked_empty p kind hM σ D hS layer hLayer y) hG

end WaveTurbulence.VineAlign
