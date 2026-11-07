/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestCaseSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertCleanupReductions
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33ReinsertReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ReinsertReduction
import Mathlib.Tactic

/-! # The reinsertion branches (rules two(c) and three(c-ii)) with optional TB cleanup

The reinsertion output keeps the forest gap minus one `L^(-γ)`, as the
source needs; the optional cleanup is a second literal deletion. Both
steps together are charged one controlled factor: their potential drop is
at most two units of 16000.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- Rule two(c): reinsertion of the separated S33 post, with the optional
TB cleanup, as one decorated replacement outcome. -/
theorem exists_s33_reinsert_outcome (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.s33.pattern)
    (hg : AppbS33SplitGeometry p.state.graph r)
    (A' : (p.state.Dart → (Fin d → ℤ)) → Prop) (hA' : ∀ κ,A' κ → p.admissible κ)
    (hT : ∀ κ,A' κ → AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ)
    (hI : S33ReinsertReduction p.state.graph r L γ δ C1 F.gap w A' p.scales)
    (hcl : AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w (appbS33SeparatedPostAdmissibility r A')
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales))) :
    ∃ (q : Problem.{u,v} V d L w c (F.gap-L^(-γ))) (k0 : ℕ),
      Nonempty (Trace p.state q.state k0) ∧ 0 < k0 ∧ GraphOk L m q.state ∧
      forestPot F-32000 ≤ forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state) ∧
      stateAct p.state ≤ stateAct q.state+60 ∧
      appbLinkCountA p.state.graph L γ δ C1 w A' p.scales ≤
        ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*q.value γ δ C1 := by
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  let q1 : Problem.{u,v} V d L w c (F.gap-L^(-γ)) :=
    { state := ofMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩)
      admissible := appbS33SeparatedPostAdmissibility r A'
      scales := appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales
      molecule := hI.molecule
      noLoops := hI.noLoops
      scales_nonneg := by
        intro S
        unfold appbReinsertScales
        split_ifs
        · exact p.scales_nonneg S
        · exact le_rfl
      validLinkScales := hI.scales c (p.validLinkScales.mono hA')
      mateLabels := hI.mateLabels
      largeGap := hI.largeGap }
  have tr1 : Trace p.state q1.state (0+1) := Trace.cons hI.step (Trace.nil _)
  have hbal1 := forestPot_edit_bound pre tail p hlist
    (BalancedStep.reinsertS33 p.state r p.molecule hg.2.1)
  have hnt1 : ∀ h : AppbNoTripleBonds q1.state.graph,GraphOk L m q1.state :=
    fun h => graphOk_of_trace hpOk tr1 h
  have e1 : q1.state = ofMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩) := rfl
  rcases hcl with hnt | htb
  · have hact1 : stateAct p.state ≤ stateAct q1.state+60 := by
      have : stateAct p.state ≤ stateAct q1.state+60*1 := stateAct_counted hI.step p.molecule q1.molecule 1 le_rfl
      linarith only [this]
    refine ⟨q1,0+1,⟨tr1⟩,Nat.succ_pos _,hnt1 hnt,?_,hact1,hI.deviation⟩
    rw [e1]
    simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one] at hbal1 ⊢
    linarith only [hbal1]
  · obtain ⟨tb⟩ := htb
    let q2 := q1.deletion tb.figure tb.labels
    have tr2 : Trace p.state q2.state (0+1+1) := Trace.cons hI.step (Trace.cons tb.step (Trace.nil _))
    have hact2 : stateAct p.state ≤ stateAct q2.state+60 :=
      stateAct_le_two hI.step tb.step p.molecule q1.molecule q2.molecule
    refine ⟨q2,0+1+1,⟨tr2⟩,Nat.succ_pos _,graphOk_of_trace hpOk tr2 tb.invariants.noTripleBonds,?_,hact2,?_⟩
    · have hbs : balancedPotential q1.state.graph+2*((0 : ℕ) : ℤ)-16000*((1 : ℕ) : ℤ) ≤
          balancedPotential tb.figure.post :=
        (BalancedStep.delete q1.state tb.kind tb.figure q1.molecule).potential_bound
      have hed : forestBalancedPotential (pre.map Problem.state++ofMolecule tb.figure.post::tail.map Problem.state)-
          forestBalancedPotential (pre.map Problem.state++q1.state::tail.map Problem.state) =
            balancedPotential tb.figure.post-balancedPotential q1.state.graph :=
        forestBalancedPotential_edit (pre.map Problem.state) (tail.map Problem.state) q1.state
          (ofMolecule tb.figure.post)
      have e : q2.state = ofMolecule tb.figure.post := rfl
      rw [e]
      rw [← e1] at hbal1
      simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,add_zero] at hbal1 hbs
      linarith only [hbal1,hbs,hed]
    · calc appbLinkCountA p.state.graph L γ δ C1 w A' p.scales
          ≤ ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*q1.value γ δ C1 := hI.deviation
        _ ≤ ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*(1*q2.value γ δ C1) := by
            gcongr; exact tb.deviation
        _ = _ := by rw [one_mul]

/-- Rule three(c-ii): reinsertion of the D33 post, with the optional
TB cleanup, as one decorated replacement outcome. -/
theorem exists_d33_reinsert_outcome (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.d33.pattern)
    (hpc : r.post.SameComponent (r.vertex 3) (r.vertex 4))
    (A' : (p.state.Dart → (Fin d → ℤ)) → Prop) (hA' : ∀ κ,A' κ → p.admissible κ)
    (hI : D33ReinsertReduction p.state.graph r L γ δ C1 F.gap w A' p.scales)
    (hcl : AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1
        (F.gap-L^(-γ)) w (r.reinsertedPostAdmissibility A' ⟨2,by decide⟩)
        (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales))) :
    ∃ (q : Problem.{u,v} V d L w c (F.gap-L^(-γ))) (k0 : ℕ),
      Nonempty (Trace p.state q.state k0) ∧ 0 < k0 ∧ GraphOk L m q.state ∧
      forestPot F-32000 ≤ forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state) ∧
      stateAct p.state ≤ stateAct q.state+60 ∧
      appbLinkCountA p.state.graph L γ δ C1 w A' p.scales ≤
        ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*q.value γ δ C1 := by
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  let q1 : Problem.{u,v} V d L w c (F.gap-L^(-γ)) :=
    { state := ofMolecule (r.directedPostWithBond 3 4 ⟨2,by decide⟩)
      admissible := r.reinsertedPostAdmissibility A' ⟨2,by decide⟩
      scales := appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales
      molecule := hI.molecule
      noLoops := hI.noLoops
      scales_nonneg := by
        intro S
        unfold appbReinsertScales
        split_ifs
        · exact p.scales_nonneg S
        · exact le_rfl
      validLinkScales := hI.scales c (p.validLinkScales.mono hA')
      mateLabels := hI.mateLabels
      largeGap := hI.largeGap }
  have tr1 : Trace p.state q1.state (0+1) := Trace.cons hI.step (Trace.nil _)
  have hbal1 := forestPot_edit_bound pre tail p hlist
    (BalancedStep.reinsertD33 p.state r p.molecule hpc)
  have hnt1 : ∀ h : AppbNoTripleBonds q1.state.graph,GraphOk L m q1.state :=
    fun h => graphOk_of_trace hpOk tr1 h
  have e1 : q1.state = ofMolecule (r.directedPostWithBond 3 4 ⟨2,by decide⟩) := rfl
  rcases hcl with hnt | htb
  · have hact1 : stateAct p.state ≤ stateAct q1.state+60 := by
      have : stateAct p.state ≤ stateAct q1.state+60*1 := stateAct_counted hI.step p.molecule q1.molecule 1 le_rfl
      linarith only [this]
    refine ⟨q1,0+1,⟨tr1⟩,Nat.succ_pos _,hnt1 hnt,?_,hact1,hI.deviation⟩
    rw [e1]
    simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one] at hbal1 ⊢
    linarith only [hbal1]
  · obtain ⟨tb⟩ := htb
    let q2 := q1.deletion tb.figure tb.labels
    have tr2 : Trace p.state q2.state (0+1+1) := Trace.cons hI.step (Trace.cons tb.step (Trace.nil _))
    have hact2 : stateAct p.state ≤ stateAct q2.state+60 :=
      stateAct_le_two hI.step tb.step p.molecule q1.molecule q2.molecule
    refine ⟨q2,0+1+1,⟨tr2⟩,Nat.succ_pos _,graphOk_of_trace hpOk tr2 tb.invariants.noTripleBonds,?_,hact2,?_⟩
    · have hbs : balancedPotential q1.state.graph+2*((0 : ℕ) : ℤ)-16000*((1 : ℕ) : ℤ) ≤
          balancedPotential tb.figure.post :=
        (BalancedStep.delete q1.state tb.kind tb.figure q1.molecule).potential_bound
      have hed : forestBalancedPotential (pre.map Problem.state++ofMolecule tb.figure.post::tail.map Problem.state)-
          forestBalancedPotential (pre.map Problem.state++q1.state::tail.map Problem.state) =
            balancedPotential tb.figure.post-balancedPotential q1.state.graph :=
        forestBalancedPotential_edit (pre.map Problem.state) (tail.map Problem.state) q1.state
          (ofMolecule tb.figure.post)
      have e : q2.state = ofMolecule tb.figure.post := rfl
      rw [e]
      rw [← e1] at hbal1
      simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,add_zero] at hbal1 hbs
      linarith only [hbal1,hbs,hed]
    · calc appbLinkCountA p.state.graph L γ δ C1 w A' p.scales
          ≤ ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*q1.value γ δ C1 := hI.deviation
        _ ≤ ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*(1*q2.value γ δ C1) := by
            gcongr; exact tb.deviation
        _ = _ := by rw [one_mul]

/-- Defective rules (two(d), three(c-ii)): the passing branch is a
reinsertion outcome, the failing branch a good deletion. Both are charged
one controlled factor. -/
theorem exists_defective_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (Test : (p.state.Dart → (Fin d → ℤ)) → Prop)
    (k : AppbPatternKind) (r : AppbRealization p.state.graph k.pattern)
    (gd : GoodDeletionReduction p.state.graph k r L γ δ η C1 w
      (fun κ => p.admissible κ ∧ ¬Test κ) p.scales)
    (hout : ∃ (q : Problem.{u,v} V d L w c (F.gap-L^(-γ))) (k0 : ℕ),
      Nonempty (Trace p.state q.state k0) ∧ 0 < k0 ∧ GraphOk L m q.state ∧
      forestPot F-32000 ≤ forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state) ∧
      stateAct p.state ≤ stateAct q.state+60 ∧
      appbLinkCountA p.state.graph L γ δ C1 w (fun κ => p.admissible κ ∧ Test κ) p.scales ≤
        ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*q.value γ δ C1)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  obtain ⟨q₁,k0,⟨tr₁⟩,hk0,hq₁,hpot,hact₁,hdev₁⟩ := hout
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  let pb := p.withAdm (fun κ => p.admissible κ ∧ ¬Test κ) (fun _ h => h.1)
  let q₂ : Problem.{u,v} V d L w c (F.gap-L^(-γ)) :=
    (pb.deletion r gd.labels).lowerGap _ (gap_step_le hL γ _)
  have tr₂ : Trace p.state q₂.state (0+1) := Trace.cons gd.step (Trace.nil _)
  have hsl := forestSlack_le F
  refine ⟨forestTwoOfReplace m hF hL pre tail p hlist q₁ q₂ le_rfl tr₁ hk0 tr₂ (Nat.succ_pos 0) hq₁
    (graphOk_deletion pb hpOk r gd.labels) 0 0 1 0 0 1
    (by push_cast; linarith only [hpot,hsl]) (by
      have := forestPot_edit_bound pre tail p hlist (BalancedStep.delete p.state k r p.molecule)
      have e : q₂.state = ofMolecule r.post := rfl
      rw [e]; simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,zero_add] at this ⊢
      linarith only [this,hsl])
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    (by push_cast; linarith only [hact₁])
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    (by
      have : stateAct p.state ≤ stateAct q₂.state+60*1 := stateAct_counted gd.step p.molecule q₂.molecule 1 le_rfl
      push_cast; linarith only [this])
    N KF KG δ C1 (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))
    (by simpa using hK) (by simpa using hK) ?_⟩
  exact (linkCountA_le_test_partition p.state.graph L γ δ C1 w p.admissible Test p.scales).trans
    (add_le_add hdev₁ gd.deviation)

end WaveTurbulence.Mole.AppbAlgorithm
