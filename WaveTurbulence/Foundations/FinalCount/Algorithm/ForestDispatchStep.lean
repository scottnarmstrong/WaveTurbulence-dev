/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestRuleTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestRuleThree
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Dispatch
import Mathlib.Tactic

/-! # One source dispatch at a connected nonterminal component (global mode) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

theorem exists_dispatch_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (hconnp : ∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b)
    (hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b)
    (dsp : Dispatch p.state.graph L γ δ η C1 w p.admissible p.scales)
    (hRI2 : ∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
      AppbS33SplitGeometry p.state.graph r → ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
      Nonempty (S33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
        (fun κ => p.admissible κ ∧ AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales))
    (hCL2 : ∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
      AppbS33SplitGeometry p.state.graph r → ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
      ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
      (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ (F.gap-L^(-γ))) →
      AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w A
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales)))
    (hRI3 : ∀ r : AppbRealization p.state.graph AppbPatternKind.d33.pattern,
      (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
      AppbD33ResidualDefect p.state.graph r →
      Nonempty (D33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
        (fun κ => p.admissible κ ∧ AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales))
    (hCL3 : ∀ r : AppbRealization p.state.graph AppbPatternKind.d33.pattern,
      (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
      ¬D33Continues r → ¬HasD33ResidualCommon r → AppbD33ResidualDefect p.state.graph r →
      ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
      (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w ζ (F.gap-L^(-γ))) →
      AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w A
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales)))
    (N KF KG : ℝ≥0∞) (hN : 1 ≤ N) (hNb : ENNReal.ofReal (Real.log L^8) ≤ N)
    (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) (hKf : ENNReal.ofReal (L^(-η/2)) ≤ KF) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  cases dsp with
  | bridge hb h =>
    obtain ⟨b⟩ := h
    exact ⟨forestOfBridge m hF hL hSl pre tail p hlist hp δ C1 _ b N KF KG hNb⟩
  | single hb h =>
    exact exists_rule_two_step m hF hL hSl pre tail p hlist hp δ C1 h hRI2 hCL2 N KF KG hN hK
  | double hb h1 r h =>
    exact exists_rule_three_step m hF hL pre tail p hlist hp δ C1 r hconnp hb hconnF (fun _ _ => hSl) h
      (hRI3 r) (hCL3 r) N KF KG hN hK
  | common hb h1 r h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp .d33same r δ C1 gd N KF KG hK⟩
  | mixedDouble hb h1 h2 k hk r h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp k r δ C1 gd N KF KG hK⟩
  | mixedSingle hb h1 h2 h4 k hk r h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp k r δ C1 gd N KF KG hK⟩
  | regularNormal hb h1 h2 h4 h32 r h =>
    obtain ⟨nr⟩ := h
    exact ⟨forestOfR3Normal m hF hL hSl pre tail p hlist hp δ C1 _ r nr N KF KG hN⟩
  | regularGood hb h1 h2 h4 h32 r t hc h =>
    obtain ⟨rg⟩ := h
    exact ⟨forestOfR32Good m hF hL pre tail p hlist hp δ C1 r t rg N KF KG hK⟩
  | fine hb h3 h =>
    obtain ⟨f⟩ := h
    exact ⟨forestOfFine m hF hL pre tail p hlist hp δ C1 f N KF KG hKf⟩

end WaveTurbulence.Mole.AppbAlgorithm
