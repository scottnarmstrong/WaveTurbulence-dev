/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenBondCounts
import Mathlib.Tactic

/-! # The degree-deficit budget for arbitrary plain gardens
TARGET `cnblock`: reducibility and pairs of trivial roots can only lower
the degree deficit. No irreducibility or positive-order premise is needed.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ}

theorem plain_garden_bonds_width_lower (G : Garden w) (hP : G.IsPlain) :
    4*G.order ≤ 2*G.molecule.bonds.card+w := by
  classical
  let BN := univ.filter (fun c : GBranch G.tree => c.1.2 ≠ [])
  let B0 := univ.filter (fun c : GBranch G.tree => c.1.2 = [])
  let L0 := univ.filter (fun l : GLeaf G.tree => l.1.2 = [])
  let LP0 := univ.filter (fun l : GLeaf G.tree => (G.pair l).1.2 = [])
  let LE := univ.filter (fun l : GLeaf G.tree =>
    G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])
  have hB : BN.card+B0.card = G.order := by
    have hh := (univ : Finset (GBranch G.tree)).card_filter_add_card_filter_not
      (fun c => c.1.2 ≠ [])
    simpa only [not_not,card_univ,card_gbranch,BN,B0,Garden.order] using hh
  have hroots : B0.card+L0.card = w := card_root_branches_add_leaves G.tree
  have hLP0 : LP0.card = L0.card := by
    apply Finset.card_bij (fun l _hl => G.pair l)
    · intro l hl
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hl).2⟩
    · intro l hl m hm he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro l hl
      exact ⟨G.pair l,mem_filter.mpr ⟨mem_univ _,by simpa only [G.pair_pair] using
        (mem_filter.mp hl).2⟩,G.pair_pair l⟩
  have hcomp : univ.filter (fun l : GLeaf G.tree =>
      ¬ (G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])) = L0 ∪ LP0 := by
    ext l
    simp only [mem_filter,mem_univ,true_and,mem_union,L0,LP0,hP l,
      true_and,not_and_or,not_not]
    tauto
  have hL : 2*G.order+w ≤ LE.card+L0.card+LP0.card := by
    have hh := (univ : Finset (GLeaf G.tree)).card_filter_add_card_filter_not
      (fun l => G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ [])
    rw [hcomp,card_univ,card_gleaf] at hh
    have hu := Finset.card_union_le L0 LP0
    change LE.card+(L0 ∪ LP0).card = 2*G.order+w at hh
    omega
  have hD : Fintype.card (GardenDart G) = BN.card*2+LE.card := by
    simp only [GardenDart,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_subtype]
    rfl
  have hE := two_mul_card_bonds G.molecule
  omega

/-- The precise degree budget used by the root-block packing argument. -/
theorem plain_garden_degree_deficit_le_width (G : Garden w) (hP : G.IsPlain) :
    ∑ v ∈ G.molecule.atoms, (4-G.molecule.deg v) ≤ w := by
  rw [Finset.sum_tsub_distrib _ (fun v _ => garden_molecule_deg_le_four G v),
    sum_degrees_eq_two_mul_bonds]
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,garden_card_atoms]
  have h := plain_garden_bonds_width_lower G hP
  omega

end WaveTurbulence.Mole
