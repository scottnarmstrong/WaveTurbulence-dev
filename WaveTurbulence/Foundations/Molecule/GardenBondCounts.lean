/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenRootCounts
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Exact garden molecule bond count and circuit rank

TARGET `propcplmol` L1304–L1306. Root leaf pairs are removed explicitly
from the LP dart count. In positive-order irreducible gardens every
trivial root pairs with a non-root leaf, giving 2E+w=4n and chi=n-R+1.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ}

/-- The actual bond count includes the trivial-tree correction internally. -/
theorem irreducible_garden_bonds_identity (G : Garden w) (hP : G.IsPlain)
    (hI : G.Irreducible) (hn : 1 ≤ G.order) :
    2*G.molecule.bonds.card+w = 4*G.order := by
  classical
  let BN := Finset.univ.filter (fun c : GBranch G.tree => c.1.2 ≠ [])
  let B0 := Finset.univ.filter (fun c : GBranch G.tree => c.1.2 = [])
  let L0 := Finset.univ.filter (fun l : GLeaf G.tree => l.1.2 = [])
  let LP0 := Finset.univ.filter (fun l : GLeaf G.tree => (G.pair l).1.2 = [])
  let LE := Finset.univ.filter (fun l : GLeaf G.tree =>
    G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])
  have hB : BN.card+B0.card = G.order := by
    have hh := (Finset.univ : Finset (GBranch G.tree)).card_filter_add_card_filter_not
      (fun c => c.1.2 ≠ [])
    simpa only [not_not,Finset.card_univ,card_gbranch,BN,B0,Garden.order] using hh
  have hroots : B0.card+L0.card = w := card_root_branches_add_leaves G.tree
  have hLP0 : LP0.card = L0.card := by
    apply Finset.card_bij (fun l _hl => G.pair l)
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    · intro l hl m hm he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro l hl
      refine ⟨G.pair l,?_,G.pair_pair l⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [G.pair_pair] using (Finset.mem_filter.mp hl).2⟩
  have hd : Disjoint L0 LP0 := by
    apply Finset.disjoint_left.mpr
    intro l hl hp
    exact irreducible_root_partner_nonroot G hP hI hn l
      (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hp).2
  have hcomp : Finset.univ.filter (fun l : GLeaf G.tree =>
      ¬ (G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])) = L0 ∪ LP0 := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,L0,LP0,
      hP l,true_and,not_and_or,not_not]
    tauto
  have hL : LE.card+L0.card+LP0.card = 2*G.order+w := by
    have hh := (Finset.univ : Finset (GLeaf G.tree)).card_filter_add_card_filter_not
      (fun l => G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])
    rw [hcomp,Finset.card_union_of_disjoint hd,Finset.card_univ,card_gleaf] at hh
    change LE.card+(L0.card+LP0.card) = 2*G.order+w at hh
    omega
  have hD : Fintype.card (GardenDart G) = BN.card*2+LE.card := by
    simp only [GardenDart,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_subtype]
    rfl
  have hE := two_mul_card_bonds G.molecule
  omega

/-- TARGET `propcplmol`: E=2n-R, stated without truncated natural subtraction. -/
theorem irreducible_garden_bonds_add_width_half {R : ℕ} (G : Garden (2*R)) (hP : G.IsPlain)
    (hI : G.Irreducible) (hn : 1 ≤ G.order) : G.molecule.bonds.card+R = 2*G.order := by
  have hh := irreducible_garden_bonds_identity G hP hI hn
  omega

/-- TARGET `propcplmol`: the actual circuit rank is n-R+1. -/
theorem irreducible_garden_circuitRank {R : ℕ} (G : Garden (2*R)) (hP : G.IsPlain)
    (hI : G.Irreducible) (hn : 1 ≤ G.order) :
    G.molecule.circuitRank = (G.order:ℤ)-(R:ℤ)+1 := by
  have hE : (G.molecule.bonds.card:ℤ)+(R:ℤ) = 2*(G.order:ℤ) := by
    exact_mod_cast irreducible_garden_bonds_add_width_half G hP hI hn
  rw [Molecule.circuitRank,garden_card_atoms,irreducible_garden_numComponents G hP hI hn]
  norm_num only [Nat.cast_one]
  linarith only [hE]

end WaveTurbulence.Mole
