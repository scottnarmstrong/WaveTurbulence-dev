/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia2
import Mathlib.Tactic

/-!
# Diamond for two `false`-choice operations at distinct members (state level)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.diamond_FF (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ false) :
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, false, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output := by
  refine ⟨⟨con.canonical, eligible_transport_false con P.elJ,
    transF_treeCoherent A i j P.hij P.c P.el P.tc P.cc con P.tcJ,
    transF_coupleCoherent A i j P.hij P.c P.el P.tc P.cc con P.ccJ, false, P.constF con hj⟩,
    ⟨hj.canonical, eligible_transport_false hj P.el,
    transF_treeCoherent A j i P.hij.symm P.c P.elJ P.tcJ P.ccJ hj P.tc,
    transF_coupleCoherent A j i P.hij.symm P.c P.elJ P.tcJ P.ccJ hj P.cc, false, P.swap.constF hj con⟩, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq (P.diamondFF_data con hj)
  · exact P.diamondFF_layered con hj

end WaveTurbulence.Stage1
