/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftAddresses
/-! Concatenated top-leaf/lower-node addresses retain both components exactly. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem top_leaf_concat_injective {w : ℕ} (top : Fin w → TTree) (a b : GLeaf top)
    (r s : TTree.Path) (h : (a.1.1, a.1.2 ++ r) = (b.1.1, b.1.2 ++ s)) : a = b ∧ r = s := by
  have hj := congrArg (fun z : Fin w × TTree.Path => z.1) h
  have hp := congrArg (fun z : Fin w × TTree.Path => z.2) h
  have ha : a.1.2 <+: a.1.2 ++ r := List.prefix_append _ _
  have hb : b.1.2 <+: a.1.2 ++ r := by
    have h0 : b.1.2 <+: b.1.2 ++ s := List.prefix_append _ _
    exact (congrArg (fun q : TTree.Path => b.1.2 <+: q) hp.symm).mp h0
  have he : a = b := by
    rcases List.prefix_or_prefix_of_prefix ha hb with h | h
    · exact GLeaf.eq_of_isDesc ⟨hj, h⟩
    · exact (GLeaf.eq_of_isDesc ⟨hj.symm, h⟩).symm
  refine ⟨he, ?_⟩
  have hpath := congrArg (fun a : GLeaf top => a.1.2) he
  exact List.append_cancel_left (hp.trans (congrArg (fun q => q ++ s) hpath.symm))

theorem graft_lower_leaf_raw_injective {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → Garden B.1.card) (B : P.parts)
    (a : GLeaf (low B).tree) (b : GLeaf (high B).tree)
    (h : ((gardenLeafEquiv top P low).symm ⟨B, a⟩).1 = ((gardenLeafEquiv top P high).symm ⟨B, b⟩).1) :
    a.1 = b.1 := by
  have ha := gardenLeafEquiv_symm_val top P low B a
  have hb := gardenLeafEquiv_symm_val top P high B b
  have hh := ha.symm.trans (h.trans hb)
  have he := top_leaf_concat_injective top
    ((blockRootEquiv top P).symm ⟨B, a.1.1⟩) ((blockRootEquiv top P).symm ⟨B, b.1.1⟩) a.1.2 b.1.2 hh
  have hr := (blockRootEquiv top P).symm.injective he.1
  exact Prod.ext (eq_of_heq (Sigma.mk.inj hr).2) he.2

theorem graft_lower_leaf_raw_congr {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → Garden B.1.card) (B : P.parts)
    (a : GLeaf (low B).tree) (b : GLeaf (high B).tree) (h : a.1 = b.1) :
    ((gardenLeafEquiv top P low).symm ⟨B, a⟩).1 = ((gardenLeafEquiv top P high).symm ⟨B, b⟩).1 := by
  have ha := gardenLeafEquiv_symm_val top P low B a
  have hb := gardenLeafEquiv_symm_val top P high B b
  have he := congrArg (fun z : Fin B.1.card × TTree.Path =>
    let ℓ := (blockRootEquiv top P).symm ⟨B, z.1⟩
    (ℓ.1.1, ℓ.1.2 ++ z.2)) h
  exact ha.trans (he.trans hb.symm)

theorem graft_lower_node_raw_congr {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → Garden B.1.card) (B : P.parts)
    (a : GNode (low B).tree) (b : GNode (high B).tree) (h : a.1 = b.1) :
    (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).1 = (gardenNodeEquiv top P high (.inr ⟨B, b⟩)).1 := by
  have ha := gardenNodeEquiv_lower_val top P low B a
  have hb := gardenNodeEquiv_lower_val top P high B b
  have he := congrArg (fun z : Fin B.1.card × TTree.Path =>
    let ℓ := (blockRootEquiv top P).symm ⟨B, z.1⟩
    (ℓ.1.1, ℓ.1.2 ++ z.2)) h
  exact ha.trans (he.trans hb.symm)

end WaveTurbulence.Induct
