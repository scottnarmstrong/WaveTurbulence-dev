/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
import Mathlib.Tactic

/-! # Exact special-bond counts after reinsertion, computed from old graph data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbAddedPairCount (M : Molecule V D) (a b u v : V) : ℕ :=
  M.bondsBetween u v + if s(a,b) = s(u,v) then 1 else 0

/-- Old degree and multiplicity test for a special bond with endpoints
u,v after adding the actual bond ab. The test contains no post statistic. -/
def AppbAddedSpecialEnds (M : Molecule V D) (a b u v : V) : Prop :=
  M.deg u+(if a = u then 1 else 0)+(if b = u then 1 else 0) = 3 ∧
  M.deg v+(if a = v then 1 else 0)+(if b = v then 1 else 0) = 3 ∧
  ∃ r ∈ insert a (insert b M.atoms),∃ s ∈ insert a (insert b M.atoms),
    r ≠ s ∧ r ≠ u ∧ r ≠ v ∧ s ≠ u ∧ s ≠ v ∧
    appbAddedPairCount M a b u v = 1 ∧ appbAddedPairCount M a b u r = 2 ∧
      appbAddedPairCount M a b v s = 2

noncomputable def appbAddedOldSpecialBonds (M : Molecule V D) (a b : V) : Finset D := by
  classical
  exact M.bonds.filter fun x => AppbAddedSpecialEnds M a b (M.atom x) (M.atom (M.mate x))

theorem appb_addBond_special_old_iff (M : Molecule V D) (a b : V) (x : D) :
    AppbSpecial (addBond M a b) (Sum.inl x) ↔ M.out x = true ∧
      AppbAddedSpecialEnds M a b (M.atom x) (M.atom (M.mate x)) := by
  change M.out x = true ∧ _ ↔ _
  simp only [AppbSpecial,AppbAddedSpecialEnds,appbAddedPairCount,
    addBond_deg,appb_addBond_bondsBetween]
  rfl

theorem appb_addBond_special_new_iff (M : Molecule V D) (a b : V) :
    AppbSpecial (addBond M a b) (Sum.inr true) ↔ AppbAddedSpecialEnds M a b a b := by
  have hu : (addBond M a b).atom (Sum.inr true) = a := rfl
  have hv : (addBond M a b).atom ((addBond M a b).mate (Sum.inr true)) = b := rfl
  have hS : (addBond M a b).atoms = insert a (insert b M.atoms) := rfl
  simp only [AppbSpecial,hu,hv,hS,addBond_deg,appb_addBond_bondsBetween]
  change (true = true ∧ _) ↔ _
  simp only [true_and,AppbAddedSpecialEnds,appbAddedPairCount]

noncomputable def appbAddedNewSpecialBonds (M : Molecule V D) (a b : V) : Finset Bool := by
  classical
  exact if AppbAddedSpecialEnds M a b a b then {true} else ∅

/-- Every old outgoing bond and the one new outgoing bond are tested
separately. Combined with atom-deletion's old-data formula this computes
the special count of each literal Appendix B reinsertion. -/
theorem appb_addBond_special_count (M : Molecule V D) (a b : V) :
    (appbSpecialBonds (addBond M a b)).card = (appbAddedOldSpecialBonds M a b).card+
      (appbAddedNewSpecialBonds M a b).card := by
  classical
  have he : appbSpecialBonds (addBond M a b) = (appbAddedOldSpecialBonds M a b).disjSum
      (appbAddedNewSpecialBonds M a b) := by
    ext x
    rcases x with x | t
    · simp [appbSpecialBonds,appbAddedOldSpecialBonds,Molecule.bonds,appb_addBond_special_old_iff]
    · cases t
      · have ho : (addBond M a b).out (Sum.inr false) = false := rfl
        by_cases h : AppbAddedSpecialEnds M a b a b <;>
          simp [appbSpecialBonds,AppbSpecial,ho,appbAddedNewSpecialBonds,h]
      · by_cases h : AppbAddedSpecialEnds M a b a b <;>
          simp [appbSpecialBonds,appb_addBond_special_new_iff,appbAddedNewSpecialBonds,h]
  rw [he,card_disjSum]

end WaveTurbulence.Mole
