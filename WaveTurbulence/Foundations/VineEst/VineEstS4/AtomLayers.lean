/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound

/-! # Atom layers are preserved by an LF operation (V5 Step 4b, R31(2))

`atomLayer_step`: for an LF operation at member `i` of a state `A`, the layer of the core branch `b` of `A` equals the layer
of the transported core branch `chosenBranchEquiv b` in the output state (`LFConstruction.coreLayers`), the layering of a
state being `stateLayer`.  Hence the cohmol atom layers (`atomLayer`) are unchanged by the twist.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS3 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.Links TTree
variable {w : ℕ} {ι : Type*}


/-- The layer of a core branch of the state, through `stateLayer`, is `layerAt` of the state's layered garden. -/
theorem atomLayer_state (A : FamilyReconstruction w ι) (b : GBranch A.skeleton.tree) :
    atomLayer A.data A.plain (stateLayer A) b = layerAt A.layered (A.data.corePosition b) := by
  have h : layerAt (layeredReconstruction A.data A.plain (stateLayer A) (stateLayer_isLayering A))
      (A.data.corePosition b) = layerAt A.layered (A.data.corePosition b) :=
    congrArg (fun LG => layerAt LG (A.data.corePosition b)) (stateLayer_spec A)
  rw [← h]
  exact (layerAt_node (layeredReconstruction A.data A.plain (stateLayer A) (stateLayer_isLayering A))
    (A.data.coreBranch A.plain b).toNode).symm

theorem atomLayer_step {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
    (op : FamilyOperation (p := p) (kind := kind) A i) (b : GBranch A.skeleton.tree) :
    atomLayer op.output.data op.output.plain (stateLayer op.output)
        (chosenBranchEquiv A.skeleton (A.family.placement i) op.choice b) =
      atomLayer A.data A.plain (stateLayer A) b :=
  (atomLayer_state op.output _).trans ((op.construction.coreLayers b).symm.trans (atomLayer_state A b).symm)

end WaveTurbulence.VineEstS4
