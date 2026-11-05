/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopNodeEmbedding
/-! Independent decoration coordinates on arbitrary grafted forests. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def graftNodeLabelsEquiv {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    (GNode (graftForest top (blockGraftTrees top P low)) → V) ≃
      (GBranch top → V) × ((B : P.parts) → GNode (low B).tree → V) :=
  (Equiv.arrowCongr (gardenNodeEquiv top P low).symm (Equiv.refl V)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ V).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.piCurry (fun B (_ : GNode (low B).tree) => V))))

theorem graftNodeLabelsEquiv_top {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → V) (b : GBranch top) :
    (graftNodeLabelsEquiv top P low κ).1 b = κ (gardenNodeEquiv top P low (.inl b)) := rfl

theorem graftNodeLabelsEquiv_lower {V : Type*} {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → V)
    (B : P.parts) (a : GNode (low B).tree) :
    (graftNodeLabelsEquiv top P low κ).2 B a = κ (lowerNodeEmbedding top P low B a) := rfl

end WaveTurbulence.Induct
