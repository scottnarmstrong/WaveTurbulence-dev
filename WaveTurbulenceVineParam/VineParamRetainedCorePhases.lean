/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedOldPhases
import Mathlib.Tactic

/-! # Signed normal-core phases survive the physical rung insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

omit [Fintype V] in
/-- Every retained core variable is its exact public contract coordinate. -/
theorem retained_core_coordinate {X : VineType} (A : Shape X) (hX : X ≠ .I)
    (hn : X.IsBad=false) {E : Type} [AddCommGroup E]
    (a b : V) (r : E) (anchor : Bool) (x : Fin (insertedShape A hX).n → E) (c : Fin 3) :
    G.insertionOldCoordinates a b r A.x0 anchor
      (fun q => x ((slotInsertionEquiv A hX).symm q)) (A.uSlot hn c)=
        x ((insertedShape A hX).uSlot hn c) :=
  G.reindexedOldCoordinate_eq A hX a b r anchor x _ _
    (slotInsertionEquiv_core A hX hn c) (uSlot_ne_reference A hn c)

/-- The common signed first core form is preserved exactly (F79). -/
theorem retained_core_first_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (hn : X.IsBad=false) (d : ℕ) (g r : Mom d)
    (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).uSlot hn 0)=
        2*((F.coreFirstSign : ℤ) : ℝ)*inner ℝ
          (x ((insertedShape F.indexing.shape hX).uSlot hn 0))
          (x ((insertedShape F.indexing.shape hX).uSlot hn 1)) := by
  erw [G.insertedContractChart_old_node F hab hX ha hb anchor d g r x _ _
    (slotInsertionEquiv_core F.indexing.shape hX hn 0) (uSlot_ne_reference F.indexing.shape hn 0)]
  rw [F.core_first_phase]
  rw [G.retained_core_coordinate,G.retained_core_coordinate]

/-- Both the linear alternative and the relatively signed nonlinear
second core form retain the exact owner-authorized coefficients (F79). -/
theorem retained_core_second_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (hn : X.IsBad=false) (d : ℕ) (g r : Mom d)
    (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).uSlot hn 1)=
        2*((F.coreFirstSign : ℤ) : ℝ)*(if F.coreLinear then
          inner ℝ (x ((insertedShape F.indexing.shape hX).uSlot hn 0))
            (x ((insertedShape F.indexing.shape hX).uSlot hn 2))
          else ((F.coreSign : ℤ) : ℝ)*inner ℝ
            (x ((insertedShape F.indexing.shape hX).uSlot hn 2))
            (x ((insertedShape F.indexing.shape hX).uSlot hn 0)+
              x ((insertedShape F.indexing.shape hX).uSlot hn 1)-
              x ((insertedShape F.indexing.shape hX).uSlot hn 2))) := by
  erw [G.insertedContractChart_old_node F hab hX ha hb anchor d g r x _ _
    (slotInsertionEquiv_core F.indexing.shape hX hn 1) (uSlot_ne_reference F.indexing.shape hn 1)]
  rw [F.core_second_phase]
  simp only [G.retained_core_coordinate]

/-- The exact core sum keeps its original ternary gap correction. -/
theorem retained_core_sum_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (hn : X.IsBad=false) (d : ℕ) (g r : Mom d)
    (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    (∑ c : Fin 3,nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).uSlot hn c))=
        2*inner ℝ r ((F.ξc 0 : ℝ) • x ((insertedShape F.indexing.shape hX).uSlot hn 0)+
          (F.ξc 1 : ℝ) • x ((insertedShape F.indexing.shape hX).uSlot hn 1)+
          (F.ξc 2 : ℝ) • x ((insertedShape F.indexing.shape hX).uSlot hn 2)+(F.ξc 3 : ℝ) • r) := by
  have hnodes := fun c : Fin 3 => G.insertedContractChart_old_node F hab hX ha hb anchor d g r x _ _
    (slotInsertionEquiv_core F.indexing.shape hX hn c) (uSlot_ne_reference F.indexing.shape hn c)
  simp_rw [hnodes]
  rw [F.core_sum_phase]
  simp only [G.retained_core_coordinate]

end WaveTurbulence.Vine.Param.RungSpliceGeometry
