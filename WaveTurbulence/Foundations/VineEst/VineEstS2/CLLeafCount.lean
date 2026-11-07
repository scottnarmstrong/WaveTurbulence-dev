/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafEnumeration
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPredecessorBudget

/-! # Exact count of the regional LP variables for sumint -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed

noncomputable def singleTreeLeafEquiv (T : TTree) : GLeaf (fun _ : Fin 1 => T) ≃ ↥T.leaves where
  toFun l := ⟨l.1.2,l.2⟩
  invFun p := ⟨(0,p.1),p.2⟩
  left_inv _l := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

theorem card_singleTreeLeaf (T : TTree) : Fintype.card (GLeaf (fun _ : Fin 1 => T)) = 2*T.order+1 := by
  have h : Fintype.card (GLeaf (fun _ : Fin 1 => T)) = T.leaves.card :=
    (Fintype.card_congr (singleTreeLeafEquiv T)).trans (Fintype.card_coe _)
  exact h.trans (Comb.card_leaves T)

/-- TARGET vineest Step2: the number of independent paired-leaf labels is
exactly the number n_(1) of integrated branch labels. This is derived from
the actual paired/boundary leaf enumeration, not assumed as a chart premise. -/
theorem card_clRegionalPairs {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : (clRegionalPairs hG U).card = clLocalOrder1 R := by
  have he := Fintype.card_congr (clLeafEquiv hU R hG)
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] at he
  have hc : Fintype.card (GLeaf (CLTreeForest R)) = 2*(clLocalOrder1 R+1)+1 :=
    (card_singleTreeLeaf (clRealizationTree R)).trans
      (congrArg (fun n => 2*n+1) (clRealizationTree_order_eq_local_add_one hU R))
  change (clRegionalPairs hG U).card*2+3 = Fintype.card (GLeaf (CLTreeForest R)) at he
  omega

end WaveTurbulence.VineEstS2
