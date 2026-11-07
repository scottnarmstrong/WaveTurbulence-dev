/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleTwoReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleThreePrimaryReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.FineReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleSixReduction
import Mathlib.Tactic

/-! # Source-priority analytic dispatch, before iterating the chosen branches -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v

inductive Dispatch {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : Prop
  | bridge (hb : ∃ e : D,Degen.IsBridge M e)
      (h : Nonempty (BridgeReduction (ofMolecule M) L γ δ C1 (L^(-γ+η)/2) w A P)) :
      Dispatch M L γ δ η C1 w A P
  | single (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h : RuleTwoReduction M L γ δ η C1 w A P) : Dispatch M L γ δ η C1 w A P
  | double (hb : ∀ e : D,¬Degen.IsBridge M e) (h1 : ¬HasDegreeThreePair M 1)
      (r : AppbRealization M AppbPatternKind.d33.pattern)
      (h : RuleThreePrimaryReduction M r L γ δ η C1 w A P) : Dispatch M L γ δ η C1 w A P
  | common (hb : ∀ e : D,¬Degen.IsBridge M e) (h1 : ¬HasDegreeThreePair M 1)
      (r : AppbRealization M AppbPatternKind.d33same.pattern)
      (h : Nonempty (GoodDeletionReduction M .d33same r L γ δ η C1 w A P)) :
      Dispatch M L γ δ η C1 w A P
  | mixedDouble (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (k : AppbPatternKind) (hk : k ∈ appbD34Kinds) (r : AppbRealization M k.pattern)
      (h : Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P)) : Dispatch M L γ δ η C1 w A P
  | mixedSingle (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2) (h4 : ¬HasThreeFourDouble M)
      (k : AppbPatternKind) (hk : k ∈ appbS32Kinds) (r : AppbRealization M k.pattern)
      (h : Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P)) : Dispatch M L γ δ η C1 w A P
  | regularNormal (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (h4 : ¬HasThreeFourDouble M) (h32 : ¬HasThreeTwo M)
      (r : AppbRealization M AppbPatternKind.r3.pattern)
      (h : Nonempty (R3NormalReduction M r L γ δ C1 (L^(-γ+η)/2) w A P)) :
      Dispatch M L γ δ η C1 w A P
  | regularGood (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (h4 : ¬HasThreeFourDouble M) (h32 : ¬HasThreeTwo M)
      (r : AppbRealization M AppbPatternKind.r3.pattern)
      (t : AppbRealization r.post AppbPatternKind.s33new3.pattern)
      (hc : M.SameComponent (r.vertex 1) (t.vertex 1))
      (h : Nonempty (R32GoodReduction M r t L γ δ η C1 w A P)) : Dispatch M L γ δ η C1 w A P
  | fine (hb : ∀ e : D,¬Degen.IsBridge M e) (h3 : ∀ a ∈ M.atoms,M.deg a ≠ 3)
      (h : Nonempty (FineReduction (ofMolecule M) L γ δ η C1 w A P)) : Dispatch M L γ δ η C1 w A P

end WaveTurbulence.Mole.AppbAlgorithm
