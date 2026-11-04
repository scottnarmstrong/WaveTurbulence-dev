/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.ActualTreeSelection
public import WaveTurbulence.Foundations.IncohInst.AncestorTimeOrder

/-! # Actual tree graph fibers and the literal internal source constraints -/

public section
noncomputable section
open scoped Classical
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh Links

@[simp] theorem tree_vertexLayer {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (v : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) :
    vertexLayer (treeLayerLinks (d := d) LG hX) v = LG.layer (treeLinkEquiv hX v).toNode := by
  rcases v with ⟨j, b⟩
  fin_cases b <;> rfl

@[simp] theorem treeClockEquiv_link {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (t : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → ℝ)
    (v : Fin (X.treeLinks (G.sig 0)).length × Fin 2) :
    treeClockEquiv hX t (treeLinkEquiv hX v) = t v.1 v.2 := by
  change treeClockEquiv hX t (treeLinkBranch hX v.1 v.2) = _
  exact treeClockEquiv_apply hX t _ _

/-- The actual graph fibers, constructed without any assumed clock estimates. -/
@[expose] def actualTreeFibers {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX) :
    TreeClockFibers C.m (treeLayerLinks (d := d) LG hX) :=
  graphTreeFibers C.selection (treeLayerLinks LG hX) (treeClockEdges hX)

/-- Source strict constraints imply every finite strict graph constraint. -/
theorem mem_treeGraph_of_internal {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden)
    {t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ}
    (ht : treeClockEquiv hX t ∈ internalTimeDomain LG) :
    t ∈ graphStrictDomain (treeLayerLinks (d := d) LG hX) (treeClockEdges hX) := by
  constructor
  · intro v
    have hv := ht (treeLinkEquiv hX v)
    rw [tree_vertexLayer]
    simpa only [treeClockEquiv_link, Int.cast_natCast] using And.intro hv.1 hv.2.1.le
  · intro v w he
    have hc := (ht (treeLinkEquiv hX w)).2.2.2 (treeLinkEquiv hX v)
      ((mem_treeClockEdges hX v w).mp he)
    simpa only [treeClockEquiv_link, Int.cast_natCast] using hc

/-- The source ancestor inequalities supply the selected-clock ordering. -/
theorem TreeClockSelection.ordered_of_internal (LG : LayeredGarden 1) {X : RegChain}
    {hX : X.DecodesTree LG.garden} (C : TreeClockSelection hX)
    {t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ}
    (ht : treeClockEquiv hX t ∈ internalTimeDomain LG) (j : Fin (C.m + 1)) :
    t (C.selection.coordinates.rootVertex j.succ).1 (C.selection.coordinates.rootVertex j.succ).2 <
      t (C.selection.coordinates.rootVertex j.castSucc).1 (C.selection.coordinates.rootVertex j.castSucc).2 := by
  have hh := branch_time_lt_of_under (treeClockEquiv hX t)
    (fun a b he => (ht a).2.2.2 b he)
    (treeLinkEquiv hX (C.selection.coordinates.rootVertex j.castSucc))
    (treeLinkEquiv hX (C.selection.coordinates.rootVertex j.succ))
    (C.adjacent j).1 (C.adjacent j).2
  simpa only [treeClockEquiv_link, Int.cast_natCast] using hh

/-- No extra source-domain premise is needed to enter the actual clock fibers. -/
theorem mem_actualTreeFibers_of_internal {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ}
    (ht : treeClockEquiv hX t ∈ internalTimeDomain LG) :
    t ∈ (actualTreeFibers (d := d) LG hX C).timeDomain :=
  mem_graphTreeFibers_of_strict_and_ordered C.selection _ _
    (mem_treeGraph_of_internal LG hX ht) (C.ordered_of_internal LG ht)

end WaveTurbulence.IncohInst
