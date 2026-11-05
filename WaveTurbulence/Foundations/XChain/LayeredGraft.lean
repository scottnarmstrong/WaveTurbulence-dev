/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTopChildren
/-! Layer transport through the concrete garden graft, including every edge and paired leaf. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def graftLayer {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (a : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden)))) : ℕ :=
  match (gardenNodeEquiv top P (fun B => (low B).garden)).symm a with
  | .inl _ => p
  | .inr z => (low z.1).layer z.2

theorem graftLayer_top {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (b : GBranch top) :
    graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden) (.inl b)) = p := by
  simp only [graftLayer, Equiv.symm_apply_apply]

theorem graftLayer_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (B : P.parts) (a : GNode (low B).garden.tree) :
    graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden) (.inr ⟨B, a⟩)) =
      (low B).layer a := by
  simp only [graftLayer, Equiv.symm_apply_apply]

/-- Layer monotonicity follows from the lower layerings and their top-level bound. -/
theorem graftLayer_child {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (hbound : ∀ B a, (low B).layer a ≤ p)
    (b : GBranch (graftForest top (blockGraftTrees top P (fun B => (low B).garden)))) (i : Fin 3) :
    graftLayer top P low p (b.child i) ≤ graftLayer top P low p b.toNode := by
  classical
  obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P (fun B => (low B).garden)).surjective b
  rcases z with b | ⟨B, b⟩
  · rw [gardenBranch_toNode_top, graftLayer_top, gardenBranch_child_top]
    unfold gardenTopChildSource
    split_ifs with h
    · exact (graftLayer_top top P low p ⟨(b.child i).1, h⟩).le
    · rw [graftLayer_lower]
      exact hbound _ _
  · rw [gardenBranch_toNode_lower, gardenBranch_child_lower, graftLayer_lower, graftLayer_lower]
    exact (low B).isLayering.1 b i

/-- The constructed garden with its transported layers is a literal LayeredGarden. -/
noncomputable def layeredGardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) : LayeredGarden w where
  garden := gardenGraft sig top P (fun B => (low B).garden) hplain hsig
  layer := graftLayer top P low p
  isLayering := by
    refine ⟨graftLayer_child top P low p hbound, ?_⟩
    intro ℓ
    obtain ⟨⟨B, a⟩, rfl⟩ := (gardenLeafEquiv top P (fun B => (low B).garden)).symm.surjective ℓ
    have hn := gardenLeaf_toNode_lower top P (fun B => (low B).garden) B a
    have hnp := gardenLeaf_toNode_lower top P (fun B => (low B).garden) B ((low B).garden.pair a)
    have hp := gardenGraft_pair_lower sig top P (fun B => (low B).garden) hplain hsig B a
    calc
      _ = graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden) (.inr ⟨B, a.toNode⟩)) :=
        congrArg (graftLayer top P low p) hn
      _ = (low B).layer a.toNode := graftLayer_lower top P low p B a.toNode
      _ = (low B).layer ((low B).garden.pair a).toNode := (low B).isLayering.2 a
      _ = graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden)
          (.inr ⟨B, ((low B).garden.pair a).toNode⟩)) :=
        (graftLayer_lower top P low p B ((low B).garden.pair a).toNode).symm
      _ = graftLayer top P low p ((gardenLeafEquiv top P (fun B => (low B).garden)).symm
          ⟨B, (low B).garden.pair a⟩).toNode := congrArg (graftLayer top P low p) hnp.symm
      _ = _ := congrArg (fun ℓ : GLeaf (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) =>
        graftLayer top P low p ℓ.toNode) hp.symm

end WaveTurbulence.Induct
