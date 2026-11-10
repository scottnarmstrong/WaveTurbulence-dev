/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedBridge
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedNormalStars
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeMolecule
import Mathlib.Tactic

/-! # A source-normal geometric envelope with derived statistic increments

Direction/decoration tests and priority scheduling refine this relation.
The index counts normal steps other than D33, whose chains can be long.
No statistic inequality is a constructor field.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive NormalGeometryStep : State.{u,v} V → State.{u,v} V → ℕ → Prop
  | bridge (s : State.{u,v} V) (e : s.Dart) (hb : Degen.IsBridge s.graph e)
      (hout : s.graph.out e = true) : NormalGeometryStep s (ofMolecule (eraseBond s.graph e)) 1
  | s33 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.s33.pattern)
      (hc : ∀ e : s.Dart,¬Degen.IsBridge s.graph e)
      (ht : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4))
      (hb : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,a ∉ AppbPatternKind.s33.pattern.removed →
        s.graph.deg (r.vertex a) = 4) : NormalGeometryStep s (ofMolecule r.post) 1
  | d33 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.d33.pattern)
      (hB : ∀ e : s.Dart,¬Degen.IsBridge s.graph e)
      (hb : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,a ∉ AppbPatternKind.d33.pattern.removed →
        s.graph.deg (r.vertex a) = 4) : NormalGeometryStep s (ofMolecule r.post) 0
  | r3 (s : State.{u,v} V) (r : AppbRealization s.graph AppbPatternKind.r3.pattern)
      (hB : ∀ e : s.Dart,¬Degen.IsBridge s.graph e)
      (hb : ∀ a ∈ AppbPatternKind.r3.pattern.vertices,a ∉ AppbPatternKind.r3.pattern.removed →
        s.graph.deg (r.vertex a) = 4)
      (hn : ∀ x : Degen.RetainedDart s.graph r.removedAtoms,
        s.graph.SameComponent (r.vertex 1) (s.graph.atom x.val) → ¬AppbSpecial r.post x) :
      NormalGeometryStep s (ofMolecule r.post) 1

theorem NormalGeometryStep.geometric {s t : State.{u,v} V} {n : ℕ}
    (h : NormalGeometryStep s t n) : GeometricStep s t := by
  cases h with
  | bridge e hb hout => exact .bridge s e
  | s33 r hc ht hb => exact .delete s .s33 r
  | d33 r hB hb => exact .delete s .d33 r
  | r3 r hB hb hn => exact .delete s .r3 r

theorem NormalGeometryStep.defect_mono {s t : State.{u,v} V} {n : ℕ}
    (h : NormalGeometryStep s t n) : defectPotential s.graph ≤ defectPotential t.graph := by
  cases h with
  | bridge e hb hout =>
    have hnu := appb_bridge_nu s.graph e hb
    have h3 := (appb_bridge_degreeThree_lower_eq s.graph e hb).1
    change defectPotential s.graph ≤ defectPotential (eraseBond s.graph e)
    unfold defectPotential
    omega
  | s33 r hc ht hb =>
    have hs := s33_normal_global_statistics s.graph r hc ht
      (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
      (hb 5 (by decide) (by decide)) (hb 6 (by decide) (by decide))
    have hnu := hs.1
    have h3 := hs.2
    change defectPotential s.graph ≤ defectPotential r.post
    unfold defectPotential
    omega
  | d33 r hB hb =>
    have hs := d33_normal_global_statistics s.graph r hB
      (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
    change defectPotential s.graph ≤ defectPotential r.post
    unfold defectPotential
    omega
  | r3 r hB hb hn =>
    have hs := r3_normal_global_statistics s.graph r hB
      (hb 2 (by decide) (by decide)) (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
    change defectPotential s.graph ≤ defectPotential r.post
    unfold defectPotential
    omega

theorem NormalGeometryStep.nonladder_balanced_gain {s t : State.{u,v} V}
    (h : NormalGeometryStep s t 1) (hM : s.graph.IsMolecule) (hno : AppbNoLoops s.graph) :
    2 ≤ balancedPotential t.graph-balancedPotential s.graph := by
  cases h with
  | bridge e hb hout => exact bridge_balanced_gain s.graph hM hno e hb hout
  | s33 r hc ht hb => exact s33_normal_balanced_gain s.graph hM r hc ht hb
  | r3 r hB hb hn => exact r3_normal_balanced_gain s.graph r hB hb hn

end WaveTurbulence.Mole.AppbAlgorithm
