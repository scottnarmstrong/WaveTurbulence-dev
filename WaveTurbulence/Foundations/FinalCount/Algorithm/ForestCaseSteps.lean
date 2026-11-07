/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestDeletionSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Dispatch
import Mathlib.Tactic

/-! # Forest step data for each source dispatch case -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c g : ℝ} {w : Mom d} {B : ℕ}

/-- A source good deletion (any kind) is a one-branch step with one
controlled factor. -/
noncomputable def forestOfGoodDeletion (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems)
    (k : AppbPatternKind) (r : AppbRealization p.state.graph k.pattern) (δ C1 : ℝ)
    (gd : GoodDeletionReduction p.state.graph k r L γ δ η C1 w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    ForestStep m F N KF KG δ C1 :=
  forestOneOfDeletion m hF hL pre tail p hlist hp r gd.labels gd.step
    (BalancedStep.delete p.state k r p.molecule) 0 0 1
    (by have := forestSlack_le F; omega) (fun h => absurd h (by norm_num))
    (fun h => absurd h (by norm_num))
    (stateAct_deletion_counted p r gd.step _ (by norm_num))
    N KF KG δ C1 _ (by simpa using hK) gd.deviation

theorem graphOk_of_trace {m : ℕ} {s t : State.{u,v} V} {n : ℕ} (hs : GraphOk L m s)
    (tr : Trace s t n) (hnt : AppbNoTripleBonds t.graph) : GraphOk L m t := by
  refine ⟨hnt,?_⟩
  have h : (t.graph.atoms.card : ℝ) ≤ s.graph.atoms.card := by exact_mod_cast tr.atomPotential_le
  exact h.trans hs.2

theorem gap_step_le (hL : 0 < L) (γ : ℝ) (g : ℝ) : g-L^(-γ) ≤ g := by
  have := Real.rpow_nonneg hL.le (-γ); linarith only [this]

/-- DH23 BR-N as a one-branch step (global-mode resource: needs no slack). -/
noncomputable def forestOfBridge (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 gp : ℝ)
    (b : BridgeReduction (ofMolecule p.state.graph) L γ δ C1 gp w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hN : ENNReal.ofReal (Real.log L^8) ≤ N) :
    ForestStep m F N KF KG δ C1 :=
  let q : Problem.{u,v} V d L w c F.gap :=
    { state := b.target
      admissible := b.admissible
      scales := b.scales
      molecule := b.molecule
      noLoops := b.noLoops
      scales_nonneg := b.scales_nonneg
      validLinkScales := b.validLinkScales c p.validLinkScales
      mateLabels := b.mateLabels
      largeGap := b.largeGapInherited F.gap p.largeGap }
  have tr : Trace p.state q.state (0+1) := Trace.cons b.step.geometric (Trace.nil _)
  forestOneOfReplace m hF hL pre tail p hlist q (gap_step_le hL γ _) tr (Nat.succ_pos 0)
    (graphOk_of_trace (graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)) tr b.noTripleBonds) 1 0 0
    (by
      have := forestPot_edit_bound pre tail p hlist (BalancedStep.normal b.step p.molecule p.noLoops)
      simp only [Nat.cast_one,Nat.cast_zero,mul_zero,sub_zero,mul_one] at this ⊢
      rw [hSl]; linarith only [this])
    (fun _ => b.step.defect_mono) (fun h => absurd h (by norm_num))
    (stateAct_counted b.step.geometric p.molecule q.molecule _ (by norm_num))
    N KF KG δ C1 _ (by simpa using hN) b.deviation

/-- DH23 2R-1F..4F, one controlled factor. -/
noncomputable def forestOfFine (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (f : FineReduction (ofMolecule p.state.graph) L γ δ η C1 w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-η/2)) ≤ KF) :
    ForestStep m F N KF KG δ C1 :=
  let q : Problem.{u,v} V d L w c F.gap :=
    { state := f.target
      admissible := f.admissible
      scales := p.scales
      molecule := f.molecule
      noLoops := f.noLoops
      scales_nonneg := p.scales_nonneg
      validLinkScales := f.validLinkScales c p.validLinkScales
      mateLabels := f.mateLabels
      largeGap := f.largeGapInherited F.gap p.largeGap }
  have tr : Trace p.state q.state (0+1) := Trace.cons f.step.geometric (Trace.nil _)
  forestOneOfReplace m hF hL pre tail p hlist q (gap_step_le hL γ _) tr (Nat.succ_pos 0)
    (graphOk_of_trace (graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)) tr f.noTripleBonds) 0 1 0
    (by
      have := forestPot_edit_bound pre tail p hlist (BalancedStep.fine f.step p.molecule)
      have h2 := forestSlack_le F
      simp only [Nat.cast_one,Nat.cast_zero,mul_zero,sub_zero,mul_one,zero_add] at this ⊢
      linarith only [this,h2])
    (fun _ => f.step.defect_mono p.molecule) (fun h => absurd h (by norm_num))
    (stateAct_counted f.step.geometric p.molecule q.molecule _ (by norm_num))
    N KF KG δ C1 _ (by simpa using hK) f.deviation

/-- DH23 3R-1N, one normal factor of size one. -/
noncomputable def forestOfR3Normal (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 gp : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.r3.pattern)
    (nr : R3NormalReduction p.state.graph r L γ δ C1 gp w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hN : 1 ≤ N) :
    ForestStep m F N KF KG δ C1 :=
  forestOneOfDeletion m hF hL pre tail p hlist hp r nr.labels nr.step.geometric
    (BalancedStep.normal nr.step p.molecule p.noLoops) 1 0 0
    (by rw [hSl]; simp) (fun _ => nr.step.defect_mono) (fun h => absurd h (by norm_num))
    (stateAct_deletion_counted p r nr.step.geometric _ (by norm_num))
    N KF KG δ C1 1 (by simpa using hN) nr.deviation

/-- DH23 3R-2G. -/
noncomputable def forestOfR32Good (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.r3.pattern)
    (t : AppbRealization r.post AppbPatternKind.s33new3.pattern)
    (rg : R32GoodReduction p.state.graph r t L γ δ η C1 w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    ForestStep m F N KF KG δ C1 :=
  let q : Problem.{u,v} V d L w c F.gap :=
    { state := ofMolecule t.post
      admissible := rg.admissible
      scales := p.scales
      molecule := rg.molecule
      noLoops := rg.noLoops
      scales_nonneg := p.scales_nonneg
      validLinkScales := rg.validLinkScales c p.validLinkScales
      mateLabels := rg.mateLabels
      largeGap := rg.largeGapInherited F.gap p.largeGap }
  have tr : Trace p.state q.state (0+1) := Trace.cons rg.step (Trace.nil _)
  forestOneOfReplace m hF hL pre tail p hlist q (gap_step_le hL γ _) tr (Nat.succ_pos 0)
    (graphOk_of_trace (graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)) tr rg.noTripleBonds) 0 0 1
    (by
      have := forestPot_edit_bound pre tail p hlist (BalancedStep.r32 p.state r t p.molecule)
      have h2 := forestSlack_le F
      simp only [Nat.cast_one,Nat.cast_zero,mul_zero,sub_zero,mul_one,zero_add] at this ⊢
      linarith only [this,h2])
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    (stateAct_counted rg.step p.molecule q.molecule _ (by norm_num))
    N KF KG δ C1 _ (by simpa using hK) rg.deviation

/-- DH23 rule two(b)/(c-i): the passing branch is the normal 3S3-1N, the
failing branch the good 3S3-2G. -/
noncomputable def forestOfRuleTwoRegular (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 gp : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.s33.pattern)
    (hN : S33NormalReduction p.state.graph r L γ δ C1 gp w
      (fun κ => p.admissible κ ∧ AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales)
    (hG : GoodDeletionReduction p.state.graph .s33 r L γ δ η C1 w
      (fun κ => p.admissible κ ∧ ¬AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) p.scales)
    (N KF KG : ℝ≥0∞) (hN1 : 1 ≤ N) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    ForestStep m F N KF KG δ C1 :=
  forestTwoOfDeletionLabels m hF hL pre tail p hlist hp
    (fun κ => AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ) r hN.labels hG.labels
    hN.step.geometric (BalancedStep.normal hN.step p.molecule p.noLoops)
    (BalancedStep.delete p.state .s33 r p.molecule) 1 0 0 0 0 1
    (by rw [hSl]; simp) (by have := forestSlack_le F; simp; omega)
    (fun _ => hN.step.defect_mono) (fun h => absurd h (by norm_num))
    (stateAct_deletion_counted p r hN.step.geometric _ (by norm_num))
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    (stateAct_deletion_counted p r hG.step _ (by norm_num))
    N KF KG δ C1 1 _
    (by simpa using hN1) (by simpa using hK) hN.deviation hG.deviation

end WaveTurbulence.Mole.AppbAlgorithm
