/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia15
import Mathlib.Tactic

/-!
# Diamond for two `true` operations (state level)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.diamondTT_layered (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    (P.constT con hj).output = (P.swap.constT hj con).output := by
  have h1 : (P.opJT con hj).output.data.Decodes (P.opJT con hj).output.plain
      (P.constT con hj).output.garden := (P.constT con hj).decodes
  have h2 : (P.opJT con hj).output.data.Decodes (P.opJT con hj).output.plain
      (P.swap.constT hj con).output.garden :=
    decodes_of_heq (P.TT_skel con hj) _ _ (P.TT_data_heq con hj) _ (P.swap.opJT hj con).output.plain
      (P.swap.constT hj con).decodes
  refine layered_eq_of_classes (p := p) (P.opJT con hj).output.data (P.opJT con hj).output.plain _ _ h1 h2
    (P.constT con hj).canonical.criterion (P.swap.constT hj con).canonical.criterion ?_ ?_ ?_
  · intro b1
    obtain ⟨b, hb⟩ := ((coreBranchEquiv A.skeleton (A.family.placement i)).trans
      ((P.srcJT con).branches true)).surjective b1
    have hb' : b1 = (P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b) := hb.symm
    rw [hb']
    exact P.TT_core con hj b
  · intro b1 q hq
    obtain ⟨b, hb⟩ := ((coreBranchEquiv A.skeleton (A.family.placement i)).trans
      ((P.srcJT con).branches true)).surjective b1
    have hb' : b1 = (P.srcJT con).branches true (coreBranchEquiv A.skeleton (A.family.placement i) b) := hb.symm
    subst hb'
    exact P.TT_tree con hj b q hq
  · intro qq1 j' r hr
    obtain ⟨qq, hqq⟩ := ((P.srcI.pairs true).trans ((P.srcJT con).pairs true)).surjective qq1
    have hqq' : qq1 = (P.srcJT con).pairs true (P.srcI.pairs true qq) := hqq.symm
    subst hqq'
    exact P.TT_couple con hj qq j' r hr

theorem PairCtx.diamond_TT (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, true, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output := by
  refine ⟨P.opJT con hj, P.swap.opJT hj con, ?_⟩
  apply familyReconstruction_ext
  · exact P.TT_skel con hj
  · exact (Sigma.mk.inj_iff.mp (P.TT_famstate con hj)).2
  · exact P.TT_data_heq con hj
  · exact P.diamondTT_layered con hj

end WaveTurbulence.Stage1
