/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutRetention
/-! Every source attachment node is exactly retained as a leaf of the inverse top forest. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem no_strict_layerCutStop_of_parentLayer_eq {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GNode LG.garden.tree) (hp : LG.parentLayer p a = p) :
    ∀ r s, a.1.2 = r ++ s → s ≠ [] → layerCutStop LG p a.1.1 r = false := by
  intro r s hrs hs
  have hpre : r <+: a.1.2 := ⟨s, hrs.symm⟩
  let u : GNode LG.garden.tree := ⟨(a.1.1, r), TTree.mem_nodes_of_prefix _ a.2 hpre⟩
  have hdesc : u.IsDesc a := ⟨rfl, hpre⟩
  have hne : u ≠ a := by
    intro he
    have hpath := congrArg (fun x : GNode LG.garden.tree => x.1.2) he
    have hlen := congrArg List.length (hpath.trans hrs)
    change r.length = (r ++ s).length at hlen
    simp only [List.length_append] at hlen
    exact hs (List.length_eq_zero_iff.mp (by omega))
  have hpath := Canon.path_ne_nil_of_isDesc_of_ne hdesc hne
  have hparent : LG.layer (Canon.par a) = p :=
    (parentLayer_eq_layer_par LG p a hpath).symm.trans hp
  have hle := LG.layer_le_of_isDesc (Canon.isDesc_par_of_isDesc_of_ne hdesc hne)
  exact (layerCutStop_false_iff LG p u).mpr (hparent.symm.trans_le hle)

theorem layerCut_attach_mem_leaves {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : GNode LG.garden.tree) (ha : a ∈ LG.attachNodes p) :
    a.1.2 ∈ (layerCutForest LG p a.1.1).leaves := by
  have hlo := (Finset.mem_filter.mp ha).2.1
  have hpar := (Finset.mem_filter.mp ha).2.2
  have hm := mem_cutTree_nodes_of_no_strict_stop (LG.garden.tree a.1.1) (layerCutStop LG p a.1.1)
    a.1.2 a.2 (no_strict_layerCutStop_of_parentLayer_eq LG p a hpar)
  rcases (TTree.mem_nodes_iff _ _).mp hm with hl | hb
  · exact hl
  · have hf := stop_false_of_mem_cutTree_branching (LG.garden.tree a.1.1) (layerCutStop LG p a.1.1) hb
    have ht := (layerCutStop_true_iff LG p a).mpr hlo
    have he := hf.symm.trans ht
    cases he

noncomputable def attachNodeToCutLeaf {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (a : ↥(LG.attachNodes p)) : GLeaf (layerCutForest LG p) :=
  ⟨a.1.1, layerCut_attach_mem_leaves LG p a.1 a.2⟩

end WaveTurbulence.Induct
