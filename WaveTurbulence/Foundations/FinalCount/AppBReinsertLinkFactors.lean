/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
public import WaveTurbulence.Foundations.FinalCount.AppBLinkLoss
import Mathlib.Tactic

/-! # Bounded ladder-weight loss under deletion followed by reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbReinsertScales (M : Molecule V D) (Y : Finset V) (a b : V)
    (P : Finset V → ℝ) (S : Finset V) : ℝ := by
  classical
  exact if S ∈ appbLinks (Degen.eraseAtoms M (Y ∪ {a,b})) then P S else 0

theorem appb_reinsert_safe_links_subset (M : Molecule V D) (Y : Finset V) (a b : V) :
    appbLinks (Degen.eraseAtoms M (Y ∪ {a,b})) ⊆ appbLinks (addBond (Degen.eraseAtoms M Y) a b) := by
  intro S hS
  obtain ⟨hlink,hdisj⟩ := (appb_link_eraseAtoms_iff M (Y ∪ {a,b}) S).mp ((mem_appbLinks _ S).mp hS)
  have hY : Disjoint S Y := hdisj.mono_right subset_union_left
  have hab : Disjoint S {a,b} := hdisj.mono_right subset_union_right
  apply (mem_appbLinks _ S).mpr
  exact appb_link_addBond_of_disjoint _ a b ((appb_link_eraseAtoms_iff M Y S).mpr ⟨hlink,hY⟩) hab

theorem appb_reinsert_post_linkProduct (M : Molecule V D) (Y : Finset V) (a b : V)
    (L γ δ : ℝ) (P : Finset V → ℝ) (hlog : 1 ≤ Real.log L) :
    appbLinkProduct (addBond (Degen.eraseAtoms M Y) a b) L γ δ (appbReinsertScales M Y a b P) =
      appbLinkProduct (Degen.eraseAtoms M (Y ∪ {a,b})) L γ δ P := by
  classical
  unfold appbLinkProduct
  symm
  calc
    _ = ∏ S ∈ appbLinks (Degen.eraseAtoms M (Y ∪ {a,b})),
        Molecule.ladderWeight L γ δ (appbReinsertScales M Y a b P S) := by
      apply prod_congr rfl
      intro S hS
      simp only [appbReinsertScales,hS,ite_true]
    _ = _ := by
      apply prod_subset (appb_reinsert_safe_links_subset M Y a b)
      intro S hS hn
      simp only [appbReinsertScales,hn,ite_false,appb_link_weight_zero hlog]

theorem appb_reinsert_linkProduct_bound (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) (a b : V) (L γ δ : ℝ) (P : Finset V → ℝ)
    (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 ≤ δ) (hP : ∀ S,0 ≤ P S) :
    appbLinkProduct M L γ δ P ≤ Real.log L^(4*(Y.card+2))*
      appbLinkProduct (addBond (Degen.eraseAtoms M Y) a b) L γ δ (appbReinsertScales M Y a b P) := by
  rw [appb_reinsert_post_linkProduct M Y a b L γ δ P hlog]
  have hb := appbLinkProduct_eraseAtoms_bound M hM (Y ∪ {a,b}) L γ δ P hL hlog hδ hP
  have hc : (Y ∪ {a,b}).card ≤ Y.card+2  := (card_union_le Y {a,b}).trans (Nat.add_le_add_left card_le_two _)
  have hp : Real.log L^(4*(Y ∪ {a,b}).card) ≤ Real.log L^(4*(Y.card+2)) :=
    pow_le_pow_right₀ hlog (by omega)
  have hn : 0 ≤ appbLinkProduct (Degen.eraseAtoms M (Y ∪ {a,b})) L γ δ P := by
    apply prod_nonneg
    intro S hS
    exact (appb_link_weight_bounds hL hlog hδ (hP S) γ).1.trans' (by norm_num)
  exact hb.trans (mul_le_mul_of_nonneg_right hp hn)

end WaveTurbulence.Mole
