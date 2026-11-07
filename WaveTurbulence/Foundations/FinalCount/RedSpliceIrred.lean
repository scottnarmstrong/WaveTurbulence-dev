/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLCN
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): a CL splice keeps a plain irreducible garden irreducible

The leaf transport of the splice preserves the tree index, and the leaves removed by the splice are
paired among themselves inside the one tree of the upper joint.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem leafEquiv_index (l : GLeaf (spliceForest G a (clSpliceBoundary hB hCL D).node)) :
    (spliceLeafEquiv (clSpliceBoundary hB hCL D) l).1.1.1 = l.1.1 := by
  obtain ⟨p, rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  rw [spliceLeafEquiv_piece]
  cases p with
  | inl l => rfl
  | inr q =>
    obtain ⟨i, q⟩ := q
    exact ((clSpliceBoundary hB hCL D).below i).1.symm

theorem clSplicedGardenOfSlots_irreducible (hP : G.IsPlain) (hI : G.Irreducible) :
    (clSplicedGardenOfSlots hB hCL D).Irreducible := by
  classical
  intro A hA hAne hcp
  refine hI A hA hAne ?_
  intro ℓ hℓ
  have hℓA : ℓ.1.1 ∈ A := by
    simpa only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and] using hℓ
  have hne : G.pair ℓ ≠ ℓ := fun h => by
    have := (G.pair_eq_iff ℓ).mp h
    exact this (hP ℓ)
  refine ⟨hne, ?_⟩
  let Bd := clSpliceBoundary hB hCL D
  by_cases hret : IsSpliceRetainedLeaf Bd ℓ
  · let ℓ' : GLeaf (clSplicedGardenOfSlots hB hCL D).tree := (spliceLeafEquiv Bd).symm ⟨ℓ, hret⟩
    have h1 : (spliceLeafEquiv Bd ℓ').1 = ℓ := by simp [ℓ']
    have hidx : ℓ'.1.1 = ℓ.1.1 := by
      have := leafEquiv_index hB hCL D ℓ'
      rw [h1] at this; exact this.symm
    have hmem : ℓ' ∈ (clSplicedGardenOfSlots hB hCL D).leavesOf A := by
      simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hidx]; exact hℓA
    have hp := (hcp ℓ' hmem).2
    have hA' : ((clSplicedGardenOfSlots hB hCL D).pair ℓ').1.1 ∈ A := by
      simpa only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hcomm := congrArg Subtype.val
      (transportedLeafPair_comm G (IsSpliceRetainedLeaf Bd) (clSignedBoundary_pair_closed hB hCL D.excluded D.kept
        D.excluded_missing D.excluded_ne_middle D.kept_ne_middle D.upper D.lower) (spliceLeafEquiv Bd) ℓ')
    have hidx2 := leafEquiv_index hB hCL D ((clSplicedGardenOfSlots hB hCL D).pair ℓ')
    have : G.pair ℓ = (spliceLeafEquiv Bd ((clSplicedGardenOfSlots hB hCL D).pair ℓ')).1 := by
      change G.pair ℓ = (spliceLeafEquiv Bd (transportedLeafPair G (IsSpliceRetainedLeaf Bd)
        (clSignedBoundary_pair_closed hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle
          D.kept_ne_middle D.upper D.lower) (spliceLeafEquiv Bd) ℓ')).1
      rw [hcomm]
      change G.pair ℓ = G.pair (spliceLeafEquiv Bd ℓ').1
      rw [h1]
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this, hidx2]
    exact hA'
  · have hdesc : a.toNode.IsDesc ℓ.toNode := by
      by_contra hn
      exact hret (Or.inl hn)
    have hℓa : a.1.1 = ℓ.1.1 := hdesc.1
    have hret2 : ¬ IsSpliceRetainedLeaf Bd (G.pair ℓ) := fun h => hret (by
      have := clSignedBoundary_pair_closed hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle
        D.kept_ne_middle D.upper D.lower (G.pair ℓ) h
      rwa [G.pair_pair] at this)
    have hdesc2 : a.toNode.IsDesc (G.pair ℓ).toNode := by
      by_contra hn
      exact hret2 (Or.inl hn)
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (G.pair ℓ).1.1 = a.1.1 := hdesc2.1.symm
    rw [this, hℓa]
    exact hℓA

end WaveTurbulence.RedSplice
