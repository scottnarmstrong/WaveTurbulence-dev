/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrT1
import Mathlib.Tactic

/-!
# The member `j` of the output of a `true`-choice operation at `i`
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

/-- Source at member `j` after a `true` operation at `i`. -/
@[expose] noncomputable def PairCtx.srcJT (con : LFConstruction P.srcI true) : LFSource p kind con.output :=
  (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).source j
    con.canonical
    (eligible_transport_true con (CoreFamily.nextPlacement_lower A.family i j) P.elJ)
    (transT_treeCoherent A i j P.hij P.c P.el P.tc P.cc con P.tcJ)
    (transT_coupleCoherent A i j P.hij P.c P.el P.tc P.cc con P.ccJ)

end WaveTurbulence.Stage1
