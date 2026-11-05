/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftAddresses
/-! Exact finite-product factorization along arbitrary grafted top and lower forests. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem prod_graft_branches {M : Type*} [CommMonoid M] {w : ℕ}
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (f : GBranch (graftForest top (blockGraftTrees top P low)) → M) :
    (∏ b, f b) = (∏ b : GBranch top, f (gardenBranchEquiv top P low (.inl b))) *
      ∏ B : P.parts, ∏ b : GBranch (low B).tree,
        f (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) := by
  have he := Fintype.prod_equiv (gardenBranchEquiv top P low)
    (fun z => f (gardenBranchEquiv top P low z)) f (fun _ => rfl)
  exact he.symm.trans (by rw [Fintype.prod_sum_type, Fintype.prod_sigma])

end WaveTurbulence.Induct
