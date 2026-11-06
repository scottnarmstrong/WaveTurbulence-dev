/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.ScaleKernel
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePairEnumeration
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePairEnumeration

/-! # The pair product of scale factors is the product over the input leaves (RA1-LEAFWISE) -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine Finset Links Incoh IncohInst

theorem prod_inputLeaves_couple_eq_pairScale {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (hG : IsCouple G) (β : Fin 2 × Path → ℝ) :
    (∏ ℓ ∈ inputLeaves G, β ℓ.1) = pairScale β (Q.pairsAt (0,[]) (1,[])) := by
  rw [inputLeaves_eq_plusLeaves hG]
  calc
    _ = ∏ ℓ : PlusLeaf G, β ℓ.val.val := Finset.prod_subtype _ (fun ℓ => mem_plusLeaves ℓ) (fun ℓ => β ℓ.1)
    _ = _ := prod_plusLeaf_eq_pair_list hQ β

theorem prod_inputLeaves_tree_eq_pairScale {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (β : Fin 1 × Path → ℝ) :
    (∏ ℓ ∈ inputLeaves G, β ℓ.1) = pairScale β (X.pairsAt (G.sig 0) ((0:Fin 1),[])) := by
  rw [tree_inputLeaves hX]
  calc
    _ = ∏ ℓ : TPlus G, β ℓ.val.val :=
        Finset.prod_subtype (plusPaired G) (fun ℓ => by simp [plusPaired]) (fun ℓ => β ℓ.1)
    _ = _ := tree_prod_TPlus_eq_pair_list hX β

end WaveTurbulence.RA1Leafwise
