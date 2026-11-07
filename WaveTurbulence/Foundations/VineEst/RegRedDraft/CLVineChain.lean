/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLIngredientGaps

/-! # Bottom-to-top CL vine ingredients and the common gap (vineest Step 1) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree

/-- An actual current connected vine with its CL labels. Type II uses the
current four-atom base template, so no m ≥ 2 restriction is introduced. -/
structure CLVineIngredient {w : ℕ} (G : Garden w) where
  atoms : Finset (GBranch G.tree)
  upperJoint : GBranch G.tree
  lowerJoint : GBranch G.tree
  vineType : VineType
  vine : G.molecule.IsVine vineType atoms upperJoint lowerJoint
  region : CLRegionData G atoms upperJoint lowerJoint

/-- Source bottom-to-top concatenation: successive ingredients share exactly
the upper/lower joint. The shared-child identity is proved, not stored. -/
def CLVineIngredient.Follows {w : ℕ} {G : Garden w} (A B : CLVineIngredient G) : Prop :=
  A.upperJoint = B.lowerJoint ∧ A.atoms ∩ B.atoms = {A.upperJoint}

noncomputable def CLVineIngredient.gap {w d : ℕ} {G : Garden w}
    (A : CLVineIngredient G) (k : GNode G.tree → Mom d) : Mom d :=
  k (A.lowerJoint.child A.region.positive)-k (A.lowerJoint.child A.region.negative)

theorem CLVineIngredient.shared_child {w : ℕ} {G : Garden w} {A B : CLVineIngredient G}
    (hf : A.Follows B) : A.upperJoint.child A.region.excluded = B.lowerJoint.child B.region.kept := by
  rcases A with ⟨SA,c,a,X,hA,RA⟩
  rcases B with ⟨SB,b,c',Y,hB,RB⟩
  change c = c' ∧ SA ∩ SB = {c} at hf
  obtain ⟨rfl,hi⟩ := hf
  exact cl_ingredient_shared_child hA.1 hB.1 RA RB hi

theorem CLVineIngredient.gap_eq {w d : ℕ} {G : Garden w} {A B : CLVineIngredient G}
    (hf : A.Follows B) (k : GNode G.tree → Mom d) (hk : IsDecoration G k) : A.gap k = B.gap k := by
  rcases A with ⟨SA,c,a,X,hA,RA⟩
  rcases B with ⟨SB,b,c',Y,hB,RB⟩
  change c = c' ∧ SA ∩ SB = {c} at hf
  obtain ⟨rfl,hi⟩ := hf
  exact cl_ingredient_gap_eq hA.1 hB.1 RA RB hi k hk

/-- Every ingredient has the same signed lower gap as the bottom ingredient. -/
theorem clVineChain_gap_eq {w d : ℕ} {G : Garden w} (A : CLVineIngredient G)
    (rest : List (CLVineIngredient G)) (hc : (A :: rest).IsChain CLVineIngredient.Follows)
    (k : GNode G.tree → Mom d) (hk : IsDecoration G k)
    (B : CLVineIngredient G) (hB : B ∈ A :: rest) : B.gap k = A.gap k := by
  rcases List.mem_cons.mp hB with rfl | hB
  · rfl
  · cases rest with
    | nil => exact (List.not_mem_nil hB).elim
    | cons C tail =>
      obtain ⟨hf,ht⟩ := List.isChain_cons_cons.mp hc
      exact (clVineChain_gap_eq C tail ht k hk B hB).trans (CLVineIngredient.gap_eq hf k hk).symm
termination_by rest.length

/-- The nondegenerate boundary case propagates without asserting that every
admissible decoration has a nonzero gap. -/
theorem clVineChain_gap_ne_zero {w d : ℕ} {G : Garden w} (A : CLVineIngredient G)
    (rest : List (CLVineIngredient G)) (hc : (A :: rest).IsChain CLVineIngredient.Follows)
    (k : GNode G.tree → Mom d) (hk : IsDecoration G k) (hgap : A.gap k ≠ 0)
    (B : CLVineIngredient G) (hB : B ∈ A :: rest) : B.gap k ≠ 0 :=
  (clVineChain_gap_eq A rest hc k hk B hB) ▸ hgap

/-- The source ± upper-gap identity, with its sign derived from the actual
root sign of each ingredient. -/
theorem clVineChain_gap_eq_upper_or_neg {w d : ℕ} {G : Garden w} (A : CLVineIngredient G)
    (rest : List (CLVineIngredient G)) (hc : (A :: rest).IsChain CLVineIngredient.Follows)
    (k : GNode G.tree → Mom d) (hk : IsDecoration G k)
    (B : CLVineIngredient G) (hB : B ∈ A :: rest) :
    A.gap k = k B.upperJoint.toNode-k (B.upperJoint.child B.region.excluded) ∨
      A.gap k = -(k B.upperJoint.toNode-k (B.upperJoint.child B.region.excluded)) := by
  have he := cl_boundary_momentum B.vine.1 B.region k hk
  change ((G.sign B.upperJoint.toNode : ℤ) : ℝ) •
    (k B.upperJoint.toNode-k (B.upperJoint.child B.region.excluded)) = B.gap k at he
  rw [clVineChain_gap_eq A rest hc k hk B hB] at he
  rcases Int.units_eq_one_or (G.sign B.upperJoint.toNode) with hs | hs
  · left
    simpa only [hs,Units.val_one,Int.cast_one,one_smul] using he.symm
  · right
    simpa only [hs,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_smul,one_smul] using he.symm

noncomputable def clBadIngredients {w : ℕ} {G : Garden w} {n : ℕ}
    (A : Fin n → CLVineIngredient G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (A i).vineType.IsBad = true)

noncomputable def clNormalIngredients {w : ℕ} {G : Garden w} {n : ℕ}
    (A : Fin n → CLVineIngredient G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (A i).vineType.IsBad = false)

theorem clBadNormal_partition {w : ℕ} {G : Garden w} {n : ℕ} (A : Fin n → CLVineIngredient G) :
    Disjoint (clBadIngredients A) (clNormalIngredients A) ∧
      clBadIngredients A ∪ clNormalIngredients A = Finset.univ := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [clBadIngredients,clNormalIngredients,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    exact Bool.noConfusion (hi.symm.trans hj)
  · ext i
    simp only [clBadIngredients,clNormalIngredients,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    cases (A i).vineType.IsBad <;> simp

end WaveTurbulence.RegRed
