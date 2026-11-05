/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MarkedGardenGraft
public import WaveTurbulence.Foundations.XChain.GraftBranchProducts
/-! Node signs and the full garden zeta factor split along arbitrary grafts. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem gardenNodeEquiv_lower_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (a : GNode (low B).tree) :
    nodeSign sig (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).1 = nodeSign (low B).sig a.1 := by
  have hv := congrArg (nodeSign sig) (gardenNodeEquiv_lower_val top P low B a)
  apply hv.trans
  change TTree.pathSign (sig ((blockRootEquiv top P).symm ⟨B, a.1.1⟩).1.1)
    (((blockRootEquiv top P).symm ⟨B, a.1.1⟩).1.2 ++ a.1.2) = _
  rw [pathSign_append]
  exact congrArg (fun ζ => TTree.pathSign ζ a.1.2) (hsig B a.1.1).symm

theorem gardenBranchEquiv_top_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) :
    nodeSign sig (gardenBranchEquiv top P low (.inl b)).toNode.1 = nodeSign sig b.toNode.1 := by
  exact congrArg (nodeSign sig) (gardenBranchEquiv_top_val top P low b)

theorem gardenBranchEquiv_lower_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (b : GBranch (low B).tree) :
    nodeSign sig (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).toNode.1 =
      nodeSign (low B).sig b.toNode.1 := by
  have he := congrArg (fun a : GNode (graftForest top (blockGraftTrees top P low)) => nodeSign sig a.1)
    (gardenBranch_toNode_lower top P low B b)
  exact he.trans (gardenNodeEquiv_lower_sign sig top P low hsig B b.toNode)

theorem markedGardenGraft_zeta {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    (markedGardenGraft sig top P low hsig).zeta =
      (∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
        ∏ B : P.parts, (low B).zeta := by
  have he := prod_graft_branches top P low
    (fun b => Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ))
  have ht := Finset.prod_congr (s₁ := (univ : Finset (GBranch top))) rfl
    (fun b _ => congrArg (fun ζ : ℤˣ => Complex.I * (((ζ : ℤˣ) : ℤ) : ℂ))
      (gardenBranchEquiv_top_sign sig top P low b))
  have hl := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl
    (fun B _ => Finset.prod_congr (s₁ := (univ : Finset (GBranch (low B).tree))) rfl
      (fun b _ => congrArg (fun ζ : ℤˣ => Complex.I * (((ζ : ℤˣ) : ℤ) : ℂ))
        (gardenBranchEquiv_lower_sign sig top P low hsig B b)))
  exact he.trans (congrArg₂ (· * ·) ht hl)

end WaveTurbulence.Induct
