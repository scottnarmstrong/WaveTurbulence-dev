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

end WaveTurbulence.Induct
