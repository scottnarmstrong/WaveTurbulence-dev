/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia8
import Mathlib.Tactic

/-!
# Diamond for a `false` operation at `i` and a `true` operation at `j` (state level)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

theorem PairCtx.diamondFT_layered (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true) :
    (P.constF con hj).output = (P.swap.constT hj con).output := by
  have hD' : (P.specF con hj).FD = (P.swap.specT hj con).FD := P.diamondFT_data con hj
  have h1 : (P.specF con hj).FD.Decodes (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain)
      (P.constF con hj).output.garden := (P.constF con hj).decodes
  have h2 : (P.specF con hj).FD.Decodes (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain)
      (P.swap.constT hj con).output.garden := by
    have := (P.swap.constT hj con).decodes
    rw [hD']
    exact this
  refine layered_eq_of_classes (p := p) (P.specF con hj).FD
    (unitTwistGarden_plain A.skeleton (A.family.placement j) A.plain) _ _ h1 h2
    (P.constF con hj).canonical.criterion (P.swap.constT hj con).canonical.criterion ?_ ?_ ?_
  · intro b'
    obtain ⟨b, rfl⟩ := (coreBranchEquiv A.skeleton (A.family.placement j)).surjective b'
    exact P.FT_core con hj b
  · intro b' q hq
    obtain ⟨b, rfl⟩ := (coreBranchEquiv A.skeleton (A.family.placement j)).surjective b'
    exact P.FT_tree con hj b q hq
  · intro qq' j' r hr
    obtain ⟨qq, rfl⟩ : ∃ qq : SourcePair A.skeleton, P.srcJ.pairs true qq = qq' :=
      (P.srcJ.pairs true).surjective qq'
    exact P.FT_couple con hj qq j' r hr

theorem PairCtx.diamond_FT (con : LFConstruction P.srcI false) (hj : LFConstruction P.srcJ true) :
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, true, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output := by
  refine ⟨⟨con.canonical, eligible_transport_false con P.elJ,
    transF_treeCoherent A i j P.hij P.c P.el P.tc P.cc con P.tcJ,
    transF_coupleCoherent A i j P.hij P.c P.el P.tc P.cc con P.ccJ, true, P.constF con hj⟩,
    ⟨hj.canonical, eligible_transport_true hj (CoreFamily.nextPlacement_lower A.family j i) P.el,
    transT_treeCoherent A j i P.hij.symm P.c P.elJ P.tcJ P.ccJ hj P.tc,
    transT_coupleCoherent A j i P.hij.symm P.c P.elJ P.tcJ P.ccJ hj P.cc, false, P.swap.constT hj con⟩, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq (P.diamondFT_data con hj)
  · exact P.diamondFT_layered con hj

theorem PairCtx.diamond_TF (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ false) :
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, false, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output := by
  obtain ⟨opi', opj', h⟩ := P.swap.diamond_FT hj con
  exact ⟨opj', opi', h.symm⟩

end WaveTurbulence.Stage1
