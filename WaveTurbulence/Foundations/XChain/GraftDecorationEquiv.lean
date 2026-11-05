/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftMatchingLabels
public import WaveTurbulence.Foundations.XChain.GraftDecoration
/-! Decoration bijection with all attachment matching constraints explicit. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

/-- A decoration of the graft is exactly a branch-consistent top decoration and lower-garden
decorations with matching root values. This includes marked lower components. -/
noncomputable def graftDecorationEquiv {V : Type*} [AddCommGroup V] {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    {κ : GNode (graftForest top (blockGraftTrees top P low)) → V //
      IsDecoration (markedGardenGraft sig top P low hsig) κ} ≃
    {x : {x : (GNode top → V) × ((B : P.parts) → GNode (low B).tree → V) //
        GraftMatching top P low x} //
      IsBranchConsistent x.1.1 ∧ ∀ B, IsDecoration (low B) (x.1.2 B)} :=
  (graftMatchingLabelsEquiv top P low).subtypeEquiv
    (fun κ => isDecoration_markedGardenGraft_iff sig top P low hsig κ)

end WaveTurbulence.Induct
