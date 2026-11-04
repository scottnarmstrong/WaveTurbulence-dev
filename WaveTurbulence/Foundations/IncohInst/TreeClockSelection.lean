/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeSpineSelection

/-! # Actual selected tree clocks, with their source ancestor geometry -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links TTree Reg

/-- Actual source addresses selected by a complete link clock selection. -/
@[expose] def selectedTreeAddress {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {r : ℕ} (S : SelectedLinkClocks (X.treeLinks (G.sig 0)).length r) (j : Fin r) : Fin 1 × Path :=
  (treeLinkEquiv hX (S.coordinates.rootVertex j)).val

/-- Exact source geometry for the root and lone-parent link clocks. -/
structure TreeClockSelection {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) where
  m : ℕ
  m_cases : m = 0 ∨ m = 2
  selection : SelectedLinkClocks (X.treeLinks (G.sig 0)).length (m + 2)
  first_eq : selectedTreeAddress hX selection 0 = (0, [])
  last_parent : ∃ i : Fin 3, (0, X.lonePath) =
    addrExt (selectedTreeAddress hX selection (Fin.last (m + 1))) [i]
  adjacent : ∀ j : Fin (m + 1),
    Under (selectedTreeAddress hX selection j.castSucc) (selectedTreeAddress hX selection j.succ) ∧
    (selectedTreeAddress hX selection j.castSucc).2.length <
      (selectedTreeAddress hX selection j.succ).2.length

theorem selectedTreeAddress_ofLinks {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {h : ℕ} (v : Fin h ↪ Fin (X.treeLinks (G.sig 0)).length) (j : Fin (h * 2)) :
    selectedTreeAddress hX (selectedClocksOfLinks v) j =
      (treeLinkBranch hX (v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2).val := by
  unfold selectedTreeAddress
  change (treeLinkEquiv hX ((rootCoordinatesOfEmbedding (selectedVerticesOfLinks v)).rootVertex j)).val = _
  rw [rootCoordinatesOfEmbedding_rootVertex]
  rfl

/-- A chain with a single top-level pair selects exactly that source link. -/
@[expose] def onePairClockSelection {G : Garden 1} (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner : RegChain) (hX : (RegChain.pair m Qr Qg inner .nil).DecodesTree G) :
    TreeClockSelection hX := by
  let X := RegChain.pair m Qr Qg inner .nil
  let l := firstSpineLink m inner ((0 : Fin 1), [])
  have hl : l ∈ spineLinks X (0, []) := firstSpineLink_mem _ _ _ _ _ _
  let v : Fin 1 ↪ Fin (X.treeLinks (G.sig 0)).length :=
    ⟨fun _ => spineLinkIndex hX l hl, fun _ _ _ => Subsingleton.elim _ _⟩
  let S := selectedClocksOfLinks v
  have he (j : Fin 2) : selectedTreeAddress hX S j = if j = 0 then l.1 else l.2 := by
    rw [selectedTreeAddress_ofLinks]
    fin_cases j <;> exact treeLinkBranch_spineLinkIndex hX l hl _
  refine ⟨0, Or.inl rfl, S, ?_, ?_, ?_⟩
  · rw [he]
    simp only [ite_true]
    rfl
  · refine ⟨m.lone, ?_⟩
    rw [he]
    simp [l, firstSpineLink, RegChain.lonePath, addrExt]
  · intro j
    fin_cases j
    simp only [he]
    norm_num
    exact ⟨(spineLink_under X (0, []) hl).2.1, spineLink_length_lt X (0, []) hl⟩

end WaveTurbulence.IncohInst
