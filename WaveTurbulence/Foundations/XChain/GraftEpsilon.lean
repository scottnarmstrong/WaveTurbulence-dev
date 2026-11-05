/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDecoration
public import WaveTurbulence.Foundations.XChain.GraftBranchProducts
/-! Exact epsilon and resonance factorization across arbitrary marked grafts. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem markedGardenGraft_epsDec {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → (Fin d → ℤ)) :
    epsDec (markedGardenGraft sig top P low hsig) κ =
      (∏ b : GBranch top,
        epsCoef (κ (topNodeEmbedding top P low (b.child 0)))
          (κ (topNodeEmbedding top P low (b.child 1)))
          (κ (topNodeEmbedding top P low (b.child 2)))) *
      ∏ B : P.parts, epsDec (low B) (fun a => κ (lowerNodeEmbedding top P low B a)) := by
  have he := prod_graft_branches top P low (fun b =>
    epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)))
  have ht := Finset.prod_congr (s₁ := (univ : Finset (GBranch top))) rfl (fun b _ =>
    congrArg₂ (fun x y => epsCoef x.1 x.2 y)
      (congrArg₂ Prod.mk (congrArg κ (topBranch_child top P low b 0))
        (congrArg κ (topBranch_child top P low b 1)))
      (congrArg κ (topBranch_child top P low b 2)))
  have hl := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ =>
    Finset.prod_congr (s₁ := (univ : Finset (GBranch (low B).tree))) rfl (fun b _ =>
      congrArg₂ (fun x y => epsCoef x.1 x.2 y)
        (congrArg₂ Prod.mk (congrArg κ (gardenBranch_child_lower top P low B b 0))
          (congrArg κ (gardenBranch_child_lower top P low B b 1)))
        (congrArg κ (gardenBranch_child_lower top P low B b 2))))
  exact he.trans (congrArg₂ (· * ·) ht hl)

theorem markedGardenGraft_omega_lower {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode (graftForest top (blockGraftTrees top P low)) → Mom d)
    (B : P.parts) (b : GBranch (low B).tree) :
    omegaNode (markedGardenGraft sig top P low hsig) k
      (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) =
      omegaNode (low B) (fun a => k (lowerNodeEmbedding top P low B a)) b := by
  have h0 := congrArg k (gardenBranch_child_lower top P low B b 0)
  have h1 := congrArg k (gardenBranch_child_lower top P low B b 1)
  have h2 := congrArg k (gardenBranch_child_lower top P low B b 2)
  have hn := congrArg k (gardenBranch_toNode_lower top P low B b)
  have hh := congrArg₂ (fun (x y : Mom d × Mom d) => resFactor x.1 x.2 y.1 y.2)
    (congrArg₂ Prod.mk h0 h1) (congrArg₂ Prod.mk h2 hn)
  exact hh

theorem markedGardenGraft_omega_top {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode (graftForest top (blockGraftTrees top P low)) → Mom d) (b : GBranch top) :
    omegaNode (markedGardenGraft sig top P low hsig) k
      (gardenBranchEquiv top P low (.inl b)) =
      resFactor (k (topNodeEmbedding top P low (b.child 0)))
        (k (topNodeEmbedding top P low (b.child 1)))
        (k (topNodeEmbedding top P low (b.child 2)))
        (k (topNodeEmbedding top P low b.toNode)) := by
  have h0 := congrArg k (topBranch_child top P low b 0)
  have h1 := congrArg k (topBranch_child top P low b 1)
  have h2 := congrArg k (topBranch_child top P low b 2)
  have hn := congrArg k ((gardenBranch_toNode_top top P low b).trans
    (topNodeEmbedding_branch top P low b).symm)
  have hh := congrArg₂ (fun (x y : Mom d × Mom d) => resFactor x.1 x.2 y.1 y.2)
    (congrArg₂ Prod.mk h0 h1) (congrArg₂ Prod.mk h2 hn)
  exact hh

end WaveTurbulence.Induct
