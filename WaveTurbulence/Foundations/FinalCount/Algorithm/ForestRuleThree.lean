/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestLadderSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestReinsertSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleThreePrimaryReduction
import Mathlib.Tactic

/-! # Rule three: step data for every primary dispatch case -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- Every constructor of the source primary rule-three dispatch yields a
step datum. The reinsertion inputs are the source reinsertion and cleanup
selectors at the forest gap; they are used only in the defective case. -/
theorem exists_rule_three_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.d33.pattern)
    (hconnp : ∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b)
    (hb : ∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e)
    (hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b)
    (hSl0 : p.state.graph.deg (r.vertex 3) = 4 → p.state.graph.deg (r.vertex 4) = 4 →
      forestSlack F = 0)
    (rt : RuleThreePrimaryReduction p.state.graph r L γ δ η C1 w p.admissible p.scales)
    (hRI : (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
      AppbD33ResidualDefect p.state.graph r →
      Nonempty (D33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
        (fun κ => p.admissible κ ∧ AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales))
    (hCL : (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
      ¬D33Continues r → ¬HasD33ResidualCommon r → AppbD33ResidualDefect p.state.graph r →
      ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
      (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w ζ (F.gap-L^(-γ))) →
      AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w A
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales)))
    (N KF KG : ℝ≥0∞) (hN : 1 ≤ N) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  cases rt with
  | wrongDirections ho h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp .d33 r δ C1 gd N KF KG hK⟩
  | continuing ho hc h =>
    obtain ⟨lr⟩ := h
    let zd : ZeroNormalData p.state :=
      { figure := r, opposite := ho, noBridges := hb, connected := hconnp, stage := .continuing hc }
    have hSl := hSl0 (zd.boundary_four 3 (by decide) (by decide))
      (zd.boundary_four 4 (by decide) (by decide))
    exact exists_continuing_step m hF hL hSl pre tail p hlist hp δ C1 _ r ho hc hb hconnp hconnF lr N KF KG hK
  | newFigure ho hc t ht h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp .d33new t δ C1 gd N KF KG hK⟩
  | commonTail ho hc hn t ht h =>
    obtain ⟨ct⟩ := h
    exact exists_common_tail_step m hF hL pre tail p hlist hp δ C1 r t ct N KF KG hK
  | defective ho hc hn' ht hdef hi hg =>
    obtain ⟨gd⟩ := hg
    have hdef' : AppbD33ResidualDefect p.state.graph r := by
      obtain ⟨b,hb1,_,hb3,hb4⟩ := hdef
      refine ⟨b,hb1,?_,?_,hb4⟩
      · intro e
        exact hb3 (e ▸ Finset.mem_image_of_mem r.vertex (by decide : (1 : ℕ) ∈ AppbPatternKind.d33.pattern.removed))
      · intro e
        exact hb3 (e ▸ Finset.mem_image_of_mem r.vertex (by decide : (2 : ℕ) ∈ AppbPatternKind.d33.pattern.removed))
    obtain ⟨hI⟩ := hRI hb ho hdef'
    have hpc : r.post.SameComponent (r.vertex 3) (r.vertex 4) :=
      d33_post_connected p.state.graph r hconnp hb _ (r.vertex_mem_post 3 (by decide) (by decide)) _
        (r.vertex_mem_post 4 (by decide) (by decide))
    let A' : (p.state.Dart → (Fin d → ℤ)) → Prop :=
      fun κ => p.admissible κ ∧ AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ
    have hcl := hCL hb ho hc ht hdef' (r.reinsertedPostAdmissibility A' ⟨2,by decide⟩) (by
      intro ζ hζ
      exact hI.largeGap ζ hζ)
    have hout := exists_d33_reinsert_outcome m hF hL pre tail p hlist hp δ C1 r hpc A' (fun _ h => h.1) hI hcl
    exact exists_defective_step m hF hL pre tail p hlist hp δ C1
      (fun κ => AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) .d33 r gd hout N KF KG hK
  | terminalRung ho hc hn ht hreg h hnext =>
    obtain ⟨nr⟩ := h
    let zd : ZeroNormalData p.state :=
      { figure := r, opposite := ho, noBridges := hb, connected := hconnp
        stage := .terminalRung hc hn ht hreg }
    have hSl := hSl0 (zd.boundary_four 3 (by decide) (by decide))
      (zd.boundary_four 4 (by decide) (by decide))
    exact ⟨forestOfTerminalRung m hF hL hSl pre tail p hlist hp δ C1 _ r hb
      (fun a ha hna => zd.boundary_four a ha hna) hreg hn hnext.1 hnext.2.1 nr N KF KG hN⟩

end WaveTurbulence.Mole.AppbAlgorithm
