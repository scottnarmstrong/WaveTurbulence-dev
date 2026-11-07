/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvGarden
import Mathlib.Tactic

/-!
# Ingredients of the maximal groups are good for a twist site

Let `S0` be an ingredient of a maximal group `Sg`.  Every maximal group is `Sg` or disjoint from it, and
every ingredient `T` of a group is `S0` or meets it in at most one atom, which is then a joint of `S0`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

theorem ing_subset {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {S T : Finset V} (h : IsIngredient M S T) : T ⊆ S := by
  rcases h with ⟨a, b, n, x, y, _, hc⟩ | ⟨a, b, e, n, x, y, _, _, _, hc⟩
  · exact (Vine.chainIngredient_spec hc).2.2
  · exact (Vine.chainIngredient_spec hc).2.2

theorem maximalGroups_disjoint {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (hM : M.IsMolecule) {S T : Finset V} (hS : S ∈ maximalGroups M)
    (hT : T ∈ maximalGroups M) (hne : S ≠ T) : Disjoint S T := by
  obtain ⟨C, hC, _⟩ := vinechainlem hM
  have := partition_eq_maximalGroups hC
  rw [← this] at hS hT
  exact hC.2.1 hS hT hne

/-- A twist site together with a maximal group of which the twisted block is an ingredient. -/
structure TwistGroupSite (G : Garden w) extends TwistSite G where
  Sg : Finset (GBranch G.tree)
  hSg : Sg ∈ maximalGroups G.molecule
  hS0 : IsIngredient G.molecule Sg S0

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite G)

theorem S0_sub : Z.S0 ⊆ Z.Sg := ing_subset Z.hS0

/-- Every maximal group is good. -/
theorem group_good {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    Z.toTwistSite.Good S := by
  by_cases h : S = Z.Sg
  · subst h; exact Or.inl Z.S0_sub
  · right
    intro x hx hxS
    exact ((Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS Z.hSg h)
      hxS) (Z.S0_sub hx)).elim

/-- An ingredient of a maximal group different from `S0` meets `S0` in at most one atom. -/
theorem sep_of_ing {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hT : IsIngredient G.molecule S T) (hTS : T ≠ Z.S0) : SeparatedGroups Z.S0 T := by
  by_cases h : S = Z.Sg
  · subst h
    intro x hx hxT y hy hyT
    exact (ing_pair (Mole.garden_isMolecule G) Z.hS0 hT (Ne.symm hTS)).1 x
      (mem_inter.mpr ⟨hx, hxT⟩) y (mem_inter.mpr ⟨hy, hyT⟩)
  · intro x hx hxT
    exact ((Finset.disjoint_left.mp
      (maximalGroups_disjoint (Mole.garden_isMolecule G) hS Z.hSg h) (ing_subset hT hxT))
      (Z.S0_sub hx)).elim

/-- Every ingredient of a maximal group is good. -/
theorem ing_good {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hT : IsIngredient G.molecule S T) : Z.toTwistSite.Good T := by
  by_cases hTS : T = Z.S0
  · subst hTS; exact Or.inl subset_rfl
  · exact Or.inr (Z.sep_of_ing hS hT hTS)

/-- An atom common to the twisted block and another ingredient is a joint of the twisted block. -/
theorem ing_joint {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hT : IsIngredient G.molecule S T) (hTS : T ≠ Z.S0) {z : GBranch G.tree}
    (hz0 : z ∈ Z.S0) (hzT : z ∈ T) : z = Z.a0 ∨ z = Z.P.lower := by
  have hSeq : S = Z.Sg := by
    by_contra h
    exact (Finset.disjoint_left.mp
      (maximalGroups_disjoint (Mole.garden_isMolecule G) hS Z.hSg h) (ing_subset hT hzT))
      (Z.S0_sub hz0)
  subst hSeq
  have hdeg := (ing_pair (Mole.garden_isMolecule G) Z.hS0 hT (Ne.symm hTS)).2 z
    (mem_inter.mpr ⟨hz0, hzT⟩)
  rcases block_degIn_cases Z.hB hz0 with ⟨h, _⟩ | ⟨_, h4⟩
  · exact h
  · omega

end TwistGroupSite
end WaveTurbulence.Stage1
