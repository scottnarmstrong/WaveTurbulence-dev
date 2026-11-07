/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvGood
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-F: at most `3^n` prescriptions on the groups of a skeleton

The maximal groups of a molecule are pairwise disjoint (S1, `maximalGroups_disjoint`, from `vinechainlem`) and non-empty,
so a skeleton of order `n` has at most `n` of them (`ncard_maximalGroups_le`), and at most `3^n` prescriptions on them
(`natCard_groupPrescription_le`).  This is the fibre bound `M = 3^N` of `pieceCount_of_rep` (TARGET L1950: "at most
`3^n` terms").
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Stage1

/-- Pairwise disjoint non-empty finsets of a finite type: at most its cardinality. -/
theorem ncard_le_of_pairwise_disjoint {α : Type*} [Fintype α] (C : Set (Finset α))
    (hne : ∀ S ∈ C, S.Nonempty) (hdisj : ∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) :
    C.ncard ≤ Fintype.card α := by
  classical
  let f : C → α := fun S => (hne S.1 S.2).choose
  have hf : Function.Injective f := by
    intro S T hST
    by_contra hne'
    have hST' : S.1 ≠ T.1 := fun h => hne' (Subtype.ext h)
    have h1 : f S ∈ S.1 := (hne S.1 S.2).choose_spec
    have h2 : f T ∈ T.1 := (hne T.1 T.2).choose_spec
    rw [hST] at h1
    exact Finset.disjoint_left.mp (hdisj S.1 S.2 T.1 T.2 hST') h1 h2
  rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective f hf

theorem ncard_maximalGroups_le {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) :
    (maximalGroups G.molecule).ncard ≤ Fintype.card (GBranch G.tree) :=
  ncard_le_of_pairwise_disjoint _ (fun S hS => hS.1.nonempty)
    (fun S hS T hT hne => maximalGroups_disjoint hM hS hT hne)

theorem natCard_gapKind : Nat.card Molecule.GapKind = 3 := by
  have e : Molecule.GapKind ≃ Fin 3 :=
    { toFun := fun k => match k with | .ZG => 0 | .SG => 1 | .LG => 2
      invFun := fun i => if i = 0 then .ZG else if i = 1 then .SG else .LG
      left_inv := fun k => by cases k <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- At most `3^{#branches}` prescriptions on the groups. -/
theorem natCard_groupPrescription_le {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) :
    Nat.card (GroupPrescription G) ≤ 3 ^ Fintype.card (GBranch G.tree) := by
  classical
  have hfin : (maximalGroups G.molecule).Finite := Set.toFinite _
  haveI : Finite (maximalGroups G.molecule) := hfin
  unfold GroupPrescription
  rw [Nat.card_fun, natCard_gapKind]
  have : Nat.card {S : Finset (GBranch G.tree) // S ∈ maximalGroups G.molecule} =
      (maximalGroups G.molecule).ncard := (Nat.card_coe_set_eq _)
  rw [this]
  exact Nat.pow_le_pow_right (by norm_num) (ncard_maximalGroups_le G hM)

end WaveTurbulence.Represents
