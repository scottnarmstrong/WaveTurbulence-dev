/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestLadderSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestReinsertSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleTwoReduction
import Mathlib.Tactic

/-! # Rule two: step data for every dispatch case -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

theorem exists_rule_two_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (rt : RuleTwoReduction p.state.graph L γ δ η C1 w p.admissible p.scales)
    (hRI : ∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
      AppbS33SplitGeometry p.state.graph r → ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
      Nonempty (S33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
        (fun κ => p.admissible κ ∧ AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales))
    (hCL : ∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
      AppbS33SplitGeometry p.state.graph r → ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
      ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
      (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ (F.gap-L^(-γ))) →
      AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w A
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales)))
    (N KF KG : ℝ≥0∞) (hN : 1 ≤ N) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  cases rt with
  | newFigure k hk r h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp k r δ C1 gd N KF KG hK⟩
  | connected hn r hc h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp .s33 r δ C1 gd N KF KG hK⟩
  | wrongDirections hn r ht ho h =>
    obtain ⟨gd⟩ := h
    exact ⟨forestOfGoodDeletion m hF hL pre tail p hlist hp .s33 r δ C1 gd N KF KG hK⟩
  | regular hn r hg hd hN' hG' =>
    obtain ⟨nr⟩ := hN'
    obtain ⟨gd⟩ := hG'
    exact ⟨forestOfRuleTwoRegular m hF hL hSl pre tail p hlist hp δ C1 _ r nr gd N KF KG hN hK⟩
  | defective hn r hg hd hI hG' =>
    obtain ⟨gd⟩ := hG'
    obtain ⟨hI'⟩ := hRI r hg hd
    let A' : (p.state.Dart → (Fin d → ℤ)) → Prop :=
      fun κ => p.admissible κ ∧ AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ
    have hcl := hCL r hg hd (appbS33SeparatedPostAdmissibility r A') (by
      intro ζ hζ
      exact hI'.largeGap ζ hζ)
    have hout := exists_s33_reinsert_outcome m hF hL pre tail p hlist hp δ C1 r hg A' (fun _ h => h.1)
      (fun _ h => h.2) hI' hcl
    exact exists_defective_step m hF hL pre tail p hlist hp δ C1
      (fun κ => AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) .s33 r gd hout N KF KG hK

end WaveTurbulence.Mole.AppbAlgorithm
