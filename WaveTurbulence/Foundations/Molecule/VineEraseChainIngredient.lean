/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
import Mathlib.Tactic

/-! # A chain's separating joints localize vertex-connected groups -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Any atom group which stays connected after deletion of any one atom
lies in a single ingredient of a containing source vine chain. -/
theorem erase_connected_in_chain_ingredient (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b : V} {n : ℕ}
    (hconn : ∀ z,GroupConnected M (A.erase z)) (h : Chain M U a b n) :
    M.IsBlock U a b → A ⊆ U →
      ∃ T p q,ChainIngredient M U a b n T p q ∧ A ⊆ T := by
  induction h with
  | single h =>
    intro _hU hAU
    exact ⟨_,_,_,ChainIngredient.single h,hAU⟩
  | @append S T a b c n hS hT hi hne ih =>
    intro hU hAU
    obtain ⟨X,hX⟩ := hT
    have hside := connected_erase_subset_side M S T A b (chain_joints_mem hS).2 hX.1.2.1 hAU
      (fun v hv hvb u hu huv => terminal_block_adj_mem M hM hX.1 hU Finset.subset_union_right hv hvb hu huv)
      (hconn b)
    rcases hside with hAS | hAT
    · obtain ⟨B,p,q,hB,hAB⟩ := ih (chain_prefix_isBlock M hM hS hX hi hU) hAS
      exact ⟨B,p,q,ChainIngredient.append_left hB ⟨X,hX⟩ hi hne,hAB⟩
    · exact ⟨T,b,c,ChainIngredient.append_last hS ⟨X,hX⟩ hi hne,hAT⟩

end WaveTurbulence.Vine
