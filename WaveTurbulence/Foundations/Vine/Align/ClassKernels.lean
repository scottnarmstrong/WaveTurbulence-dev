/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.ClassShape
public import WaveTurbulence.Foundations.Vine.Align.MemberKernels
/-! Native outer-slot invariance for every genuine member of the finite class. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine

section ClassKernelsMk
variable {w p d : ℕ} {kind : Bool} {S : Garden w}
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

/-- B1b-3 (Mk-general form of `classShape_slotFn`).
R-SLOT as equality of the actual native kernel functions, with no invariance premise. -/
theorem classShape_slotFnMk (hG : (stSt S σ Mk).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot (stSt S σ Mk).G) :
    slotFn y.1.data y.1.plain L γ δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((classShapeMk hM σ D hS layer hLayer hp y hy hT).iota y.1.plain hG s) =
    slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) f) layer hLayer
      ((stShape hM σ Mk).iota hS hG s) :=
  commonShape_slotFnMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1
    (hT _ (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2) hG f L γ δ s

end ClassKernelsMk

variable {w p d : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssembly hM σ)))
  (hy : y ∈ classU (unitsSplit (alignedAssembly hM σ)) p kind
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)))

end WaveTurbulence.VineAlign
