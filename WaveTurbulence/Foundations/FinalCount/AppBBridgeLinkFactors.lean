/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondLinkPreservation
public import WaveTurbulence.Foundations.FinalCount.AppBLinkLoss
import Mathlib.Tactic

/-! # A uniform logarithmic ladder-factor bound for bridge removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Keep the scales on links avoiding both endpoints; all other post links
receive scale zero and therefore weight one. -/
noncomputable def appbBridgeScales (M : Molecule V D) (e : D) (P : Finset V → ℝ)
    (S : Finset V) : ℝ := by
  classical
  exact if S ∈ appbLinks (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}) then P S else 0

theorem appb_bridge_post_linkProduct (M : Molecule V D) (e : D) (L γ δ : ℝ)
    (P : Finset V → ℝ) (hlog : 1 ≤ Real.log L) :
    appbLinkProduct (eraseBond M e) L γ δ (appbBridgeScales M e P) =
      appbLinkProduct (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}) L γ δ P := by
  classical
  unfold appbLinkProduct
  symm
  calc
    _ = ∏ S ∈ appbLinks (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}),
        Molecule.ladderWeight L γ δ (appbBridgeScales M e P S) := by
      apply prod_congr rfl
      intro S hS
      simp only [appbBridgeScales,hS,ite_true]
    _ = _ := by
      apply prod_subset (appb_endpoint_deleted_links_subset M e)
      intro S hS hn
      simp only [appbBridgeScales,hn,ite_false,appb_link_weight_zero hlog]

/-- A bridge removal loses at most four old link weights. This supplies
the source normal bound uniformly in graph size; retaining extra old
links would only strengthen it. -/
theorem appb_bridge_linkProduct_bound (M : Molecule V D) (hM : M.IsMolecule) (e : D)
    (L γ δ : ℝ) (P : Finset V → ℝ) (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : 0 ≤ δ) (hP : ∀ S,0 ≤ P S) :
    appbLinkProduct M L γ δ P ≤ Real.log L^8*
      appbLinkProduct (eraseBond M e) L γ δ (appbBridgeScales M e P) := by
  rw [appb_bridge_post_linkProduct M e L γ δ P hlog]
  have hb := appbLinkProduct_eraseAtoms_bound M hM {M.atom e,M.atom (M.mate e)} L γ δ P hL hlog hδ hP
  have hc : ({M.atom e,M.atom (M.mate e)} : Finset V).card ≤ 2 := card_le_two
  have hp : Real.log L^(4*({M.atom e,M.atom (M.mate e)} : Finset V).card) ≤ Real.log L^8 :=
    pow_le_pow_right₀ hlog (by omega)
  have hn : 0 ≤ appbLinkProduct (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}) L γ δ P := by
    apply prod_nonneg
    intro S hS
    exact (appb_link_weight_bounds hL hlog hδ (hP S) γ).1.trans' (by norm_num)
  exact hb.trans (mul_le_mul_of_nonneg_right hp hn)

end WaveTurbulence.Mole
