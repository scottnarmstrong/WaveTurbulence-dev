/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeGraphBoundary
public import WaveTurbulence.Foundations.Incoh.RootCoordinatesOfEmbedding
public import WaveTurbulence.Foundations.Incoh.SelectedClockDomain

/-! # Actual tree root and lone-parent coordinates -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The actual two extreme selected vertices form the root/lone-parent clock embedding. -/
@[expose] def TreeClockSelection.extremeEmbedding {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) :
    Fin 2 ↪ (Fin (X.treeLinks (G.sig 0)).length × Fin 2) where
  toFun i := C.selection.coordinates.rootVertex (if i = 0 then 0 else Fin.last (C.m + 1))
  inj' := by
    intro i j he
    have hh := congrArg (fun v => C.selection.coordinates.permutation (finProdFinEquiv v)) he
    simp only [RootCoordinates.rootVertex, Equiv.apply_symm_apply] at hh
    have hi := Sum.inl.inj hh
    fin_cases i <;> fin_cases j
    · rfl
    · have hval := congrArg Fin.val hi
      norm_num at hval
    · have hval := congrArg Fin.val hi
      norm_num at hval
    · rfl

/-- No root-coordinate field is assumed: the actual extreme vertices construct the split. -/
@[expose] def TreeClockSelection.rootCoordinates {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) : RootCoordinates (X.treeLinks (G.sig 0)).length :=
  rootCoordinatesOfEmbedding C.extremeEmbedding

theorem TreeClockSelection.rootCoordinates_first {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) :
    C.rootCoordinates.rootVertex 0 = C.selection.coordinates.rootVertex 0 := by
  rw [TreeClockSelection.rootCoordinates, rootCoordinatesOfEmbedding_rootVertex]
  rfl

theorem TreeClockSelection.rootCoordinates_last {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) :
    C.rootCoordinates.rootVertex 1 = C.selection.coordinates.rootVertex (Fin.last (C.m + 1)) := by
  rw [TreeClockSelection.rootCoordinates, rootCoordinatesOfEmbedding_rootVertex]
  rfl

end WaveTurbulence.IncohInst
