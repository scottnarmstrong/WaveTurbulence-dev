/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayeredGraft
public import WaveTurbulence.Foundations.XChain.LowerEmbeddings
public import WaveTurbulence.Foundations.Canon.Basic
/-! Parent addresses of internal lower nodes are preserved by the concrete graft. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem lowerNode_path_ne_nil {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GNode (low B).tree) (ha : a.1.2 ≠ []) :
    (lowerNodeEmbedding top P low B a).1.2 ≠ [] := by
  have hv := gardenNodeEquiv_lower_val top P low B a
  have hp := congrArg (fun z : Fin w × TTree.Path => z.2) hv
  intro hn
  have hnil := hp.symm.trans hn
  exact ha (List.append_eq_nil_iff.mp hnil).2

theorem lowerNode_par {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GNode (low B).tree) (ha : a.1.2 ≠ []) :
    Canon.par (lowerNodeEmbedding top P low B a) =
      lowerNodeEmbedding top P low B (Canon.par a) := by
  apply Subtype.ext
  have hv := gardenNodeEquiv_lower_val top P low B a
  have hp := gardenNodeEquiv_lower_val top P low B (Canon.par a)
  change ((lowerNodeEmbedding top P low B a).1.1,
    (lowerNodeEmbedding top P low B a).1.2.dropLast) = _
  have he := congrArg (fun z : Fin w × TTree.Path => (z.1, z.2.dropLast)) hv
  exact he.trans ((by
    simp only [Canon.par, List.dropLast_append_of_ne_nil ha] :
      (((blockRootEquiv top P).symm ⟨B, a.1.1⟩).1.1,
        (((blockRootEquiv top P).symm ⟨B, a.1.1⟩).1.2 ++ a.1.2).dropLast) =
      (((blockRootEquiv top P).symm ⟨B, (Canon.par a).1.1⟩).1.1,
        ((blockRootEquiv top P).symm ⟨B, (Canon.par a).1.1⟩).1.2 ++ (Canon.par a).1.2)).trans hp.symm)

theorem parentLayer_eq_layer_par {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GNode LG.garden.tree) (ha : a.1.2 ≠ []) :
    LG.parentLayer p a = LG.layer (Canon.par a) := by
  simp only [LayeredGarden.parentLayer, ha, ite_false, Canon.par]

theorem graft_parentLayer_internal {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (B : P.parts) (a : GNode (low B).garden.tree) (ha : a.1.2 ≠ []) (q : ℕ) :
    (layeredGardenGraft sig top P low p hplain hsig hbound).parentLayer p
      (lowerNodeEmbedding top P (fun B => (low B).garden) B a) =
      (low B).parentLayer q a := by
  have hg := parentLayer_eq_layer_par
    (layeredGardenGraft sig top P low p hplain hsig hbound) p
    (lowerNodeEmbedding top P (fun B => (low B).garden) B a)
    (lowerNode_path_ne_nil top P (fun B => (low B).garden) B a ha)
  have hl := parentLayer_eq_layer_par (low B) q a ha
  have he := lowerNode_par top P (fun B => (low B).garden) B a ha
  exact hg.trans (((congrArg (graftLayer top P low p) he).trans
    (graftLayer_lower top P low p B (Canon.par a))).trans hl.symm)

end WaveTurbulence.Induct
