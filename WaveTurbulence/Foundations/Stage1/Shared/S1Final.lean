/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia16
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvFamily
import Mathlib.Tactic

/-!
# Congruence is an equivalence relation on `IsVFamily` states (GAP.congEquiv)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- The Diamond for any two admissible operations at distinct members (all four choice combinations). -/
theorem diamond_all : DiamondProp p kind w ι :=
  diamondProp_of_TT (fun _ _ _ P con hj => P.diamond_TT con hj)

/-- **`OpsCommute`** (locality of LF operations at distinct members). -/
theorem opsCommute_all : OpsCommute p kind w ι := opsCommute_of_diamond diamond_all

/-- **Congruence is an equivalence relation** (on all states). -/
theorem congruent_equivalence [Fintype ι] [DecidableEq ι] :
    Equivalence (Congruent (w := w) (ι := ι) p kind) :=
  congruent_equivalence_of_commute opsCommute_all

/-- Congruence preserves `IsVFamily`. -/
theorem congruent_isVFamily [Fintype ι] {A B : FamilyReconstruction w ι}
    (h : Congruent (w := w) (ι := ι) p kind A B) (hA : IsVFamily A) : IsVFamily B := by
  obtain ⟨M, _, hM⟩ := h
  exact isVFamily_batch hM hA

/-- **GAP.congEquiv**: congruence is an equivalence relation on `IsVFamily` states. -/
theorem congruent_equivalence_isVFamily [Fintype ι] [DecidableEq ι] :
    Equivalence (fun A B : {A : FamilyReconstruction w ι // IsVFamily A} =>
      Congruent (w := w) (ι := ι) p kind A.1 B.1) :=
  ⟨fun A => (congruent_equivalence (p := p) (kind := kind)).refl A.1,
   fun h => (congruent_equivalence (p := p) (kind := kind)).symm h,
   fun h1 h2 => (congruent_equivalence (p := p) (kind := kind)).trans h1 h2⟩

end WaveTurbulence.Stage1
