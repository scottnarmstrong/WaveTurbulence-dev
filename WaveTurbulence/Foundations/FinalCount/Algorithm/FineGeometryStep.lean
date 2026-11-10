/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeTwoSelection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalNuEffects
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBCommonExteriorDegrees
import Mathlib.Tactic

/-! # Actual fine-operation geometry and derived resource bounds

This envelope records old figure degrees. It neither assumes a counting
estimate nor replaces the source priority selector or decoration tests.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]
variable {D : Type u} [Fintype D] [DecidableEq D]

def FineProfile (M : Molecule V D) (k : AppbPatternKind) (r : AppbRealization M k.pattern) : Prop :=
  match k with
  | .r21 => M.deg (r.vertex 2) = 4
  | .r22 => M.deg (r.vertex 2) = 4 ∧ (M.deg (r.vertex 3) = 2 ∨ M.deg (r.vertex 3) = 4)
  | .r23 => M.deg (r.vertex 4) ≠ 3 ∧ M.deg (r.vertex 5) ≠ 3
  | .r23triangle | .r24 => True
  | _ => False

inductive FineGeometryStep : State.{u,v} V → State.{u,v} V → Prop
  | table (s : State.{u,v} V) (k : AppbPatternKind)
      (hk : k ∈ ([AppbPatternKind.r21,.r22,.r23,.r23triangle,.r24] : List _))
      (r : AppbRealization s.graph k.pattern) (hp : FineProfile s.graph k r)
      (hB : ∀ e : s.Dart,¬Degen.IsBridge s.graph e) : FineGeometryStep s (ofMolecule r.post)
  | common (s : State.{u,v} V) (r : AppbRealization s.graph appbR23Common)
      (hp : s.graph.deg (r.vertex 4) ≠ 3)
      (hB : ∀ e : s.Dart,¬Degen.IsBridge s.graph e) : FineGeometryStep s (ofMolecule r.post)

theorem FineGeometryStep.geometric {s t : State.{u,v} V} (h : FineGeometryStep s t) : GeometricStep s t := by
  cases h with
  | table k hk r hp hB => exact .delete s k r
  | common r hp hB => exact .common s r

theorem fine_table_defect_mono (M : Molecule V D) (hM : M.IsMolecule) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.r21,.r22,.r23,.r23triangle,.r24] : List _))
    (r : AppbRealization M k.pattern) (hp : FineProfile M k r)
    (hB : ∀ e : D,¬Degen.IsBridge M e) : defectPotential M ≤ defectPotential r.post := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · have hnu := r21_global_nu_change M r hB
    have h3 := appb_r21_degreeThree M r hp
    unfold defectPotential
    omega
  · have hnu := r22_global_nu_change M r hB
    have h3 := appb_r22_degreeThree M r hp.1 hp.2
    unfold defectPotential
    split_ifs at h3 <;> omega
  · have hnu := r23_global_nu_change M r hB
    have h3 := appb_r23_degreeThree M r hp.1 hp.2
    unfold defectPotential
    split_ifs at h3 <;> omega
  · have hnu := r23triangle_global_nu_change M r
    have h3 := appb_r23triangle_degreeThree M r
    unfold defectPotential
    omega
  · have hnu := r24_global_nu_change M r
    have h3 := appb_r24_degreeThree M r
    unfold defectPotential
    omega

theorem FineGeometryStep.defect_mono {s t : State.{u,v} V} (h : FineGeometryStep s t)
    (hM : s.graph.IsMolecule) : defectPotential s.graph ≤ defectPotential t.graph := by
  cases h with
  | table k hk r hp hB => exact fine_table_defect_mono s.graph hM k hk r hp hB
  | common r hp hB =>
    have hnu := r23common_global_nu_change s.graph r hB
    have h3 := appb_r23_common_degreeThree s.graph r (deg_le_four s.graph hM (r.vertex_mem 4 (by decide))) hp
    change defectPotential s.graph ≤ defectPotential r.post
    unfold defectPotential
    omega

theorem FineGeometryStep.balanced_drop_le {s t : State.{u,v} V} (h : FineGeometryStep s t)
    (hM : s.graph.IsMolecule) : balancedPotential s.graph-8000 ≤ balancedPotential t.graph := by
  cases h with
  | table k hk r hp hB => exact pattern_deletion_balanced_drop_le s.graph hM k r
  | common r hp hB => exact common_deletion_balanced_drop_le s.graph hM r

end WaveTurbulence.Mole.AppbAlgorithm
