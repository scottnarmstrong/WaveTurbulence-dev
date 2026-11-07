/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF5
import Mathlib.Tactic

/-!
# The glue specification transporting a construction across a `false`-choice operation at another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

theorem core_lower_base {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool) :
    (s.baseData ε).corePosition (s.branches ε s.placement.lower) =
      inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode := by
  unfold ReconstructionData.corePosition
  rw [baseData_tree_lower s ε]
  simp [RegChain.lonePath, addrExt_nil]

theorem core_lower_pin {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool) :
    layerAt LG (s.data.corePosition s.placement.lower) =
      layerAt (s.base ε) (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        (s.branches ε s.placement.lower).toNode) := by
  rw [← core_lower_base]
  exact (k2_pins s ε).1 _

/-- Data of two members `i ≠ j` of a state, both admissible for an operation. -/
structure PairCtx (p : ℕ) (kind : Bool) {w : ℕ} {ι : Type*} (A : FamilyReconstruction w ι) (i j : ι) where
  hij : i ≠ j
  c : CanonicalObject p kind A.layered
  el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i)
  tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode))
  cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))
  elJ : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement j)
      (A.family.kind j) (A.family.atoms j) (A.family.upper j)
  tcJ : CohOn A.layered ((A.data.tree (A.family.placement j).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement j).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement j).lower.toNode))
  ccJ : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).secondLeaf A.plain).toNode))

namespace PairCtx
variable {A : FamilyReconstruction w ι} {i j : ι} (P : PairCtx p kind A i j)

@[expose] def srcI : LFSource p kind A.layered := A.source i P.c P.el P.tc P.cc
@[expose] def srcJ : LFSource p kind A.layered := A.source j P.c P.elJ P.tcJ P.ccJ

/-- Source at member `j` after a `false` operation at `i`. -/
@[expose] noncomputable def srcJF (con : LFConstruction P.srcI false) : LFSource p kind con.output :=
  srcAfterF A i j P.hij P.c P.el P.tc P.cc con P.elJ P.tcJ P.ccJ

end PairCtx

end WaveTurbulence.Stage1
