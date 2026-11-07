/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairPriority
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33SwapComponents
public import WaveTurbulence.Foundations.FinalCount.AppBS33CanonicalSplit
public import WaveTurbulence.Foundations.FinalCount.AppBS33GraphEffects
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # All source rule-two geometric decisions, including actual reindexing -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

inductive RuleTwoGeometry (M : Molecule V D) : Prop
  | newFigure (h : NewSinglePairFigure M) : RuleTwoGeometry M
  | connected (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern)
      (hc : ∀ a ∈ r.post.atoms,∀ b ∈ r.post.atoms,r.post.SameComponent a b) : RuleTwoGeometry M
  | wrongDirections (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (ht : AppbS33SplitTopology M r)
      (ho : ¬(AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val ∧
        AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨2,by decide⟩).val (r.edge ⟨4,by decide⟩).val)) : RuleTwoGeometry M
  | regular (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
      (hd : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,
        a ∉ AppbPatternKind.s33.pattern.removed → M.deg (r.vertex a) = 4) : RuleTwoGeometry M
  | defective (hn : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
      (hd : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4)) : RuleTwoGeometry M

/-- DH23 algorithm rule two(a)--(d), before partitioning the actual
source decoration tests. Reindexings are actual realizations, not WLOG
assumptions on degrees or on the split components. -/
theorem exists_rule_two_geometry (M : Molecule V D)
    (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (h : RuleTwoFigure M) : RuleTwoGeometry M := by
  classical
  cases h with
  | newFigure h => exact .newFigure h
  | primary hn r =>
    have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hc
    rcases appb_s33_remove_graph_effect M .s33 (by decide) r hc hb with hF | hF
    · have hF' : r.post.numComponents = 1 := hF.1.trans hm
      exact .connected hn r (fun a ha b hb => appb_connected_of_numComponents_eq_one r.post hF' ha hb)
    · have hF' : r.post.numComponents = 2 := by omega
      obtain ⟨t,ht,htop⟩ := appb_s33_canonical_split_exists M r hc hb hF'
      by_cases ho : AppbOppositeFrom M (t.vertex 1) (t.vertex 2) (t.edge ⟨1,by decide⟩).val (t.edge ⟨3,by decide⟩).val ∧
          AppbOppositeFrom M (t.vertex 1) (t.vertex 2) (t.edge ⟨2,by decide⟩).val (t.edge ⟨4,by decide⟩).val
      · have hg : AppbS33SplitGeometry M t := ⟨htop.1,htop.2.1,htop.2.2,ho.1,ho.2⟩
        by_cases hd : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,
            a ∉ AppbPatternKind.s33.pattern.removed → M.deg (t.vertex a) = 4
        · exact .regular hn t hg hd
        · obtain ⟨z,hz,hgeom,hdef⟩ := exists_s33_left_defective t hg hd
          exact .defective hn z hgeom hdef
      · exact .wrongDirections hn t htop ho

end WaveTurbulence.Mole.AppbAlgorithm
