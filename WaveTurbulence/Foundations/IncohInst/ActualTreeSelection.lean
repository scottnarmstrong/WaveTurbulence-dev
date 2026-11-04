/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeTwoLinkSelection
public import WaveTurbulence.Foundations.IncohInst.TreeSourceGraph

/-! # The fully constructed actual source tree clock selection -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links TTree Reg

/-- Every nontrivial actual regular tree supplies the required two or four clocks. -/
@[expose] def actualTreeSelection {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (hne : X ≠ .nil) : TreeClockSelection hX := by
  cases X with
  | nil => exact False.elim (hne rfl)
  | pair m Qr Qg inner rest =>
    cases rest with
    | nil => exact onePairClockSelection m Qr Qg inner hX
    | pair m' Qr' Qg' inner' rest' =>
      exact twoLinkClockSelection m Qr Qg inner (.pair m' Qr' Qg' inner' rest') (by simp) hX

/-- Selected source path lengths increase strictly with the selected index. -/
theorem TreeClockSelection.strictMono_length {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) :
    StrictMono (fun j => (selectedTreeAddress hX C.selection j).2.length) :=
  Fin.strictMono_iff_lt_succ.mpr (fun j => (C.adjacent j).2)

/-- Actual parent-child edges between selected vertices have the required index orientation. -/
theorem TreeClockSelection.edge_index {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) (i j : Fin (C.m + 2))
    (he : (C.selection.coordinates.rootVertex i, C.selection.coordinates.rootVertex j) ∈ treeClockEdges hX) :
    j < i := by
  have hc := (mem_treeClockEdges hX _ _).mp he
  obtain ⟨_, k, hk⟩ := hc
  have hl := congrArg List.length hk
  have hij : (selectedTreeAddress hX C.selection j).2.length <
      (selectedTreeAddress hX C.selection i).2.length := by
    dsimp only [selectedTreeAddress]
    simp only [List.length_append, List.length_singleton] at hl
    omega
  exact C.strictMono_length.lt_iff_lt.mp hij

end WaveTurbulence.IncohInst
