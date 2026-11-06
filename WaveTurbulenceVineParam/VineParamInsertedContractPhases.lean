/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedContractChart
public import WaveTurbulenceVineParam.VineParamAnchoredJointPhase
public import WaveTurbulenceVineParam.VineParamNormalizedCertificatePhases
import Mathlib.Tactic

/-! # Exact contract node phases of the newly inserted paired rung -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Actual-bond energy of the inserted chart is literally directed energy
of its inverse, at every actual source atom. -/
theorem insertedContractChart_energy {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d)
    (v : V ⊕ Fin 2) :
    energy (graphMolecule G.newEnds) univ
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 v=
    directedEnergy G.newEnds v
      ((G.anchoredInsertionChart a b hab ha hb r (G.oldDirectedChart F hab g r)
        F.indexing.shape.x0 anchor).symm
          (fun i => x ((slotInsertionEquiv F.indexing.shape hX).symm i))).1 := by
  erw [graph_energy]
  congr 1

/-- The actual fresh s atom has exactly the negative bilinear phase. -/
theorem insertedContractChart_s_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m))=
      -2*inner ℝ
        (x ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m)))
        (x ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m))) := by
  change energy (graphMolecule G.newEnds) univ
    ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1
      ((G.insertedIndexing F.indexing hX ha hb).atom _).1+
        (if (insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m)=
          (insertedShape F.indexing.shape hX).x0 then _ else 0)=_
  erw [G.insertedIndexing_new_y,ite_eq_right (ySlot_ne_reference _ _),add_zero,
    G.insertedContractChart_energy,G.anchoredInsertionChart_s_phase]
  have hx := (slotInsertionEquiv F.indexing.shape hX).symm_apply_apply
    ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m))
  have hy := (slotInsertionEquiv F.indexing.shape hX).symm_apply_apply
    ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m))
  erw [slotInsertionEquiv_new_x] at hx
  erw [slotInsertionEquiv_new_y] at hy
  erw [hx,hy]

/-- The actual fresh t atom has precisely the positive bilinear phase
and its source ternary correction in the physical joint gap. -/
theorem insertedContractChart_t_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m))=
      2*inner ℝ
        (x ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m)))
        (x ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m)))+
      2*inner ℝ r
        ((G.pattern.contractCorrection (G.gapSign a b) 0 : ℝ) •
          x ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m))+
        (G.pattern.contractCorrection (G.gapSign a b) 1 : ℝ) •
          x ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m))+
        (G.pattern.contractCorrection (G.gapSign a b) 2 : ℝ) • r) := by
  change energy (graphMolecule G.newEnds) univ
    ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1
      ((G.insertedIndexing F.indexing hX ha hb).atom _).1+
        (if (insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m)=
          (insertedShape F.indexing.shape hX).x0 then _ else 0)=_
  erw [G.insertedIndexing_new_x,ite_eq_right (xSlot_ne_reference _ _),add_zero,
    G.insertedContractChart_energy,G.anchoredInsertionChart_t_phase]
  have hx := (slotInsertionEquiv F.indexing.shape hX).symm_apply_apply
    ((insertedShape F.indexing.shape hX).xSlot (Fin.last F.indexing.shape.m))
  have hy := (slotInsertionEquiv F.indexing.shape hX).symm_apply_apply
    ((insertedShape F.indexing.shape hX).ySlot (Fin.last F.indexing.shape.m))
  erw [slotInsertionEquiv_new_x] at hx
  erw [slotInsertionEquiv_new_y] at hy
  erw [hx,hy]

/-- Directed and contract energies of the old inverse coincide. -/
theorem oldDirectedChart_energy {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (d : ℕ) (g r : Mom d) (x : Fin F.indexing.shape.n → Mom d) (v : V) :
    directedEnergy G.ends v ((G.oldDirectedChart F hab g r).symm x).1=
      energy (graphMolecule G.ends) univ ((F.chart g r).symm x).1 v := by
  erw [graph_energy]
  rfl

/-- At the physical anchor side, the actual included-joint phase is
preserved exactly, including its boundary norm correction. -/
theorem insertedContractChart_joint_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb (decide (b ∈ G.cap)) g r).symm x).1 g r
      (insertedShape F.indexing.shape hX).x0=
        2*inner ℝ r (x (insertedShape F.indexing.shape hX).x0) := by
  have hphase : ∀ z,directedEnergy G.ends b ((G.oldDirectedChart F hab g r).symm z).1+
      ‖g‖^2-‖g-r‖^2=2*inner ℝ r (z F.indexing.shape.x0) := by
    intro z
    erw [G.oldDirectedChart_energy]
    have h := F.joint_phase d g r z
    simp only [nodeResonance,F.indexing.lower,ite_true] at h
    simpa only [add_sub_assoc] using h
  change energy (graphMolecule G.newEnds) univ
    ((G.insertedContractChart F hab hX ha hb (decide (b ∈ G.cap)) g r).symm x).1
      ((G.insertedIndexing F.indexing hX ha hb).atom _).1+
        (‖g‖^2-‖g-r‖^2)=_
  erw [(G.insertedIndexing F.indexing hX ha hb).lower,G.insertedContractChart_energy]
  have h := G.anchoredInsertionChart_joint_of_old a b hab ha hb g r
    (G.oldDirectedChart F hab g r) F.indexing.shape.x0 hphase
      (fun i => x ((slotInsertionEquiv F.indexing.shape hX).symm i))
  have hx := (slotInsertionEquiv F.indexing.shape hX).symm_apply_apply
    (insertedShape F.indexing.shape hX).x0
  erw [slotInsertionEquiv_reference] at hx
  erw [hx] at h
  simpa only [add_sub_assoc] using h

end WaveTurbulence.Vine.Param.RungSpliceGeometry
