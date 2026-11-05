/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftAddresses
/-! Top edges either stay in the top branching region or enter one lower root. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def gardenTopChildSource {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) (i : Fin 3) : GBranch top ⊕ (Σ B : P.parts, GNode (low B).tree) := by
  classical
  exact if h : (b.child i).1.2 ∈ (top (b.child i).1.1).branching then
    .inl ⟨(b.child i).1, h⟩
  else
    let ha := ((TTree.mem_nodes_iff _ _).mp (b.child i).2).resolve_right h
    let a : GLeaf top := ⟨(b.child i).1, ha⟩
    let z := blockRootEquiv top P a
    .inr ⟨z.1, GNode.root (low z.1).tree z.2⟩

theorem gardenBranch_child_top {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) (i : Fin 3) :
    (gardenBranchEquiv top P low (.inl b)).child i =
      gardenNodeEquiv top P low (gardenTopChildSource top P low b i) := by
  classical
  unfold gardenTopChildSource
  split_ifs with h
  · apply Subtype.ext
    exact (congrArg (fun x : Fin w × TTree.Path => (x.1, x.2 ++ [i]))
      (gardenBranchEquiv_top_val top P low b)).trans
        (gardenNodeEquiv_top_val top P low ⟨(b.child i).1, h⟩).symm
  · let ha := ((TTree.mem_nodes_iff _ _).mp (b.child i).2).resolve_right h
    let a : GLeaf top := ⟨(b.child i).1, ha⟩
    let z := blockRootEquiv top P a
    have hInv : (blockRootEquiv top P).symm z = a := (blockRootEquiv top P).symm_apply_apply a
    have hroot : (gardenNodeEquiv top P low (.inr ⟨z.1, GNode.root (low z.1).tree z.2⟩)).1 =
        (b.child i).1 := by
      have hval := gardenNodeEquiv_lower_val top P low z.1 (GNode.root (low z.1).tree z.2)
      have hraw : (let ℓ := (blockRootEquiv top P).symm z
          (ℓ.1.1, ℓ.1.2 ++ ([] : TTree.Path))) = (b.child i).1 := by
        simp only [List.append_nil]
        exact congrArg (fun ℓ : GLeaf top => ℓ.1) hInv
      exact hval.trans hraw
    apply Subtype.ext
    exact (congrArg (fun x : Fin w × TTree.Path => (x.1, x.2 ++ [i]))
      (gardenBranchEquiv_top_val top P low b)).trans hroot.symm


theorem gardenGraft_pair_eq {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (ℓ : GLeaf (graftForest top (blockGraftTrees top P low))) :
    (gardenGraft sig top P low hplain hsig).pair ℓ =
      (gardenLeafEquiv top P low).symm (blockPair low (gardenLeafEquiv top P low ℓ)) := rfl

theorem gardenGraft_pair_lower {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    (gardenGraft sig top P low hplain hsig).pair ((gardenLeafEquiv top P low).symm ⟨B, ℓ⟩) =
      (gardenLeafEquiv top P low).symm ⟨B, (low B).pair ℓ⟩ := by
  rw [gardenGraft_pair_eq, Equiv.apply_symm_apply]
  rfl

end WaveTurbulence.Induct
