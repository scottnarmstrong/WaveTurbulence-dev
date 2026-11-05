/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftData
public import WaveTurbulence.Foundations.XChain.LayerCutForest
public import WaveTurbulence.Foundations.XChain.TreeCutGraftBoundary
/-! The source layer cut recovers the exact top trees of any canonical construction datum. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem isCanonG_layer_lt {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG p LG)
    (a : GNode LG.garden.tree) : LG.layer a < p := by
  cases p with
  | zero => exact False.elim h
  | succ q => exact Nat.lt_succ_of_le (h.2.2.2.1 a)

theorem canonicalGraftData_stop_branch {w p : ℕ} {sig : Fin w → ℤˣ}
    (C : CanonicalGraftData sig p) (b : GBranch C.top) : layerCutStop C.graft p b.1.1 b.1.2 = false := by
  have ht := graftLayer_top C.top C.partition C.low p b
  have hp := (layerCutStop_false_iff C.graft p (gardenNodeEquiv C.top C.partition
    (fun B => (C.low B).garden) (.inl b))).mpr ht.ge
  exact hp

theorem canonicalGraftData_stop_leaf {w p : ℕ} {sig : Fin w → ℤˣ}
    (C : CanonicalGraftData sig p) (a : GLeaf C.top) :
    blockGraftTrees C.top C.partition (fun B => (C.low B).garden) a.1.1 a.1.2 = TTree.leaf ∨
      layerCutStop C.graft p a.1.1 a.1.2 = true := by
  let z := blockRootEquiv C.top C.partition a
  rcases C.component z.1 with hc | hp
  · right
    let r := GNode.root (C.low z.1).garden.tree z.2
    let n := gardenNodeEquiv C.top C.partition (fun B => (C.low B).garden) (.inr ⟨z.1, r⟩)
    have hl := (graftLayer_lower C.top C.partition C.low p z.1 r).trans_lt (isCanonG_layer_lt hc r)
    have hs := (layerCutStop_true_iff C.graft p n).mpr hl
    have hv := gardenNodeEquiv_lower_val C.top C.partition (fun B => (C.low B).garden) z.1 r
    have he := (blockRootEquiv C.top C.partition).symm_apply_apply a
    have hraw : n.1 = a.1 := by
      have hi := congrArg (fun l : GLeaf C.top => (l.1.1, l.1.2 ++ ([] : TTree.Path))) he
      exact hv.trans (hi.trans (by simp only [List.append_nil]))
    have hstop := congrArg (fun x : Fin w × TTree.Path => layerCutStop C.graft p x.1 x.2) hraw
    exact hstop.symm.trans hs
  · exact Or.inl ((blockGraftTrees_at_leaf C.top C.partition (fun B => (C.low B).garden) a).trans (hp.2.1 z.2))

theorem canonicalGraftData_layerCutForest {w p : ℕ} {sig : Fin w → ℤˣ}
    (C : CanonicalGraftData sig p) : layerCutForest C.graft p = C.top := by
  funext j
  exact cutTree_graft_boundary (C.top j) (blockGraftTrees C.top C.partition (fun B => (C.low B).garden) j)
    (layerCutStop C.graft p j)
    (fun a ha => canonicalGraftData_stop_branch C ⟨(j, a), ha⟩)
    (fun a ha => canonicalGraftData_stop_leaf C ⟨(j, a), ha⟩)

end WaveTurbulence.Induct
