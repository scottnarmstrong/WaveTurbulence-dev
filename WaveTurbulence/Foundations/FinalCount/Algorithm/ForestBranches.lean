/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestSetting
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestReplace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestProgress
import Mathlib.Tactic

/-! # Forest step data from actual component edits, splits and discards -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

def GraphOk (L : ℝ) (m : ℕ) (s : State.{u,v} V) : Prop :=
  AppbNoTripleBonds s.graph ∧ (s.graph.atoms.card : ℝ) ≤ (1+Real.log L)^m

theorem forestOk_of_global (m : ℕ) (F : CountingForest.{u,v} V d L γ η w c B)
    (hm : F.mode = .globalScan) (h : ∀ s ∈ F.graphs,GraphOk L m s) : ForestOk m F := by
  refine ⟨fun p hp => h p.state (List.mem_map_of_mem hp),?_⟩
  rw [hm]; trivial

theorem graphOk_of_forestOk {m : ℕ} {F : CountingForest.{u,v} V d L γ η w c B}
    (h : ForestOk m F) : ∀ s ∈ F.graphs,GraphOk L m s := by
  intro s hs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
  exact h.1 p hp

/-- The branch obtained by replacing one component by a decorated problem
through a nonempty trace, followed by the global mode. -/
noncomputable def replaceBranch (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) (n kf kg : ℕ)
    (hres : forestPot F+forestSlack F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤
      forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state))
    (hdef : kg = 0 → defectPotential p.state.graph ≤ defectPotential q.state.graph)
    (hprog : n+kf+kg = 0 → p.state.graph.bonds.Nonempty → q.state.graph.bonds.Nonempty)
    (hact : stateAct p.state ≤ stateAct q.state+60*((n : ℤ)+kf+kg)) :
    ForestBr m F :=
  have hGg : (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs =
      pre.map Problem.state++q.state::tail.map Problem.state :=
    F.replace_graphs pre tail p hlist q tr hk0 hL.le hg
  have hmode : (F.replace pre tail p hlist q tr hk0 hL.le hg).mode = .globalScan := rfl
  have hGok : ForestOk m (F.replace pre tail p hlist q tr hk0 hL.le hg) := by
    refine forestOk_of_global m _ hmode ?_
    rw [hGg]
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
      exact graphOk_of_forestOk hF _ (List.mem_map_of_mem (hlist ▸ List.mem_append_left _ hp'))
    · rcases List.mem_cons.mp h with rfl | h
      · exact hq
      · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
        exact graphOk_of_forestOk hF _
          (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp')))
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  have hphi : forestPhi (F.replace pre tail p hlist q tr hk0 hL.le hg)+1 ≤ forestPhi F := by
    unfold forestPhi
    rw [hGg,hFg]
    exact forestBonds_trace_decrease _ _ tr hk0
  ⟨F.replace pre tail p hlist q tr hk0 hL.le hg,n,kf,kg,
    F.replace_weight_lt pre tail p hlist q tr hk0 hL.le hg,hGok,by
    have := forestSlack_global _ hmode
    change _ ≤ forestBalancedPotential (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs+
      forestSlack (F.replace pre tail p hlist q tr hk0 hL.le hg)
    rw [hGg,this]
    simpa only [add_zero] using hres,
    fun h0 => by
      have h1 := forestDefect_edit (pre.map Problem.state) (tail.map Problem.state) p.state q.state
      change forestDefectPotential F.graphs ≤
        forestDefectPotential (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs
      rw [hGg,hFg]
      linarith only [h1,hdef h0],
    fun hb => by
      by_cases hz : n+kf+kg = 0
      · right
        change ListBonds (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs
        rw [hGg]
        exact listBonds_edit (hprog hz) (hFg ▸ hb)
      · exact Or.inl (Nat.pos_of_ne_zero hz),
    by omega,
    forestAct_replace pre tail p hlist q.state hGg hact⟩

theorem replaceBranch_phi_lt (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) (n kf kg : ℕ) (hres hdef hprog hact) :
    forestPhi (replaceBranch m hF hL pre tail p hlist q hg tr hk0 hq n kf kg hres hdef hprog hact).G <
      forestPhi F := by
  have hGg : (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs =
      pre.map Problem.state++q.state::tail.map Problem.state :=
    F.replace_graphs pre tail p hlist q tr hk0 hL.le hg
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  change forestBonds (F.replace pre tail p hlist q tr hk0 hL.le hg).graphs < forestBonds F.graphs
  rw [hGg,hFg]
  have := forestBonds_trace_decrease (pre.map Problem.state) (tail.map Problem.state) tr hk0
  omega

theorem replaceBranch_value (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) (n kf kg : ℕ) (hres hdef hprog hact) (δ C1 : ℝ) :
    (replaceBranch m hF hL pre tail p hlist q hg tr hk0 hq n kf kg hres hdef hprog hact).G.value δ C1 =
      (pre.map fun p => p.value γ δ C1).prod*q.value γ δ C1*(tail.map fun p => p.value γ δ C1).prod :=
  F.replace_value pre tail p hlist q tr hk0 hL.le hg δ C1

theorem forest_value_eq (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (δ C1 : ℝ) :
    F.value δ C1 = (pre.map fun p => p.value γ δ C1).prod*p.value γ δ C1*
      (tail.map fun p => p.value γ δ C1).prod := by
  simp only [CountingForest.value,hlist,List.map_append,List.map_cons,List.prod_append,List.prod_cons,mul_assoc]

/-- One-branch step datum from a local value bound. -/
noncomputable def forestOneOfReplace (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) (n kf kg : ℕ)
    (hres : forestPot F+forestSlack F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤
      forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state))
    (hdef : kg = 0 → defectPotential p.state.graph ≤ defectPotential q.state.graph)
    (hprog : n+kf+kg = 0 → p.state.graph.bonds.Nonempty → q.state.graph.bonds.Nonempty)
    (hact : stateAct p.state ≤ stateAct q.state+60*((n : ℤ)+kf+kg))
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) (I : ℝ≥0∞) (hI : I ≤ N^n*KF^kf*KG^kg)
    (hloc : p.value γ δ C1 ≤ I*q.value γ δ C1) :
    ForestStep m F N KF KG δ C1 :=
  .one (replaceBranch m hF hL pre tail p hlist q hg tr hk0 hq n kf kg hres hdef hprog hact) (by
    rw [forest_value_eq F pre tail p hlist]
    unfold ForestBranch.term
    rw [replaceBranch_value m hF hL pre tail p hlist q hg tr hk0 hq n kf kg hres hdef hprog hact]
    calc _ ≤ (pre.map fun p => p.value γ δ C1).prod*(I*q.value γ δ C1)*
          (tail.map fun p => p.value γ δ C1).prod := by gcongr
      _ ≤ _ := by
        have : I*q.value γ δ C1 ≤ N^n*KF^kf*KG^kg*q.value γ δ C1 := by gcongr
        calc _ ≤ (pre.map fun p => p.value γ δ C1).prod*(N^n*KF^kf*KG^kg*q.value γ δ C1)*
              (tail.map fun p => p.value γ δ C1).prod := by gcongr
          _ = _ := by dsimp only [replaceBranch]; ring)

/-- Two-branch step datum (the label split): the two decorated outcomes
replace the same component. -/
noncomputable def forestTwoOfReplace (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q₁ q₂ : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k₁ k₂ : ℕ} (tr₁ : Trace p.state q₁.state k₁) (hk₁ : 0 < k₁)
    (tr₂ : Trace p.state q₂.state k₂) (hk₂ : 0 < k₂)
    (hq₁ : GraphOk L m q₁.state) (hq₂ : GraphOk L m q₂.state)
    (n₁ kf₁ kg₁ n₂ kf₂ kg₂ : ℕ)
    (hres₁ : forestPot F+forestSlack F+2*(n₁ : ℤ)-48000*((kf₁ : ℤ)+kg₁) ≤
      forestBalancedPotential (pre.map Problem.state++q₁.state::tail.map Problem.state))
    (hres₂ : forestPot F+forestSlack F+2*(n₂ : ℤ)-48000*((kf₂ : ℤ)+kg₂) ≤
      forestBalancedPotential (pre.map Problem.state++q₂.state::tail.map Problem.state))
    (hdef₁ : kg₁ = 0 → defectPotential p.state.graph ≤ defectPotential q₁.state.graph)
    (hprog₁ : n₁+kf₁+kg₁ = 0 → p.state.graph.bonds.Nonempty → q₁.state.graph.bonds.Nonempty)
    (hact₁ : stateAct p.state ≤ stateAct q₁.state+60*((n₁ : ℤ)+kf₁+kg₁))
    (hdef₂ : kg₂ = 0 → defectPotential p.state.graph ≤ defectPotential q₂.state.graph)
    (hprog₂ : n₂+kf₂+kg₂ = 0 → p.state.graph.bonds.Nonempty → q₂.state.graph.bonds.Nonempty)
    (hact₂ : stateAct p.state ≤ stateAct q₂.state+60*((n₂ : ℤ)+kf₂+kg₂))
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) (I₁ I₂ : ℝ≥0∞) (hI₁ : I₁ ≤ N^n₁*KF^kf₁*KG^kg₁)
    (hI₂ : I₂ ≤ N^n₂*KF^kf₂*KG^kg₂)
    (hloc : p.value γ δ C1 ≤ I₁*q₁.value γ δ C1+I₂*q₂.value γ δ C1) :
    ForestStep m F N KF KG δ C1 :=
  .two (replaceBranch m hF hL pre tail p hlist q₁ hg tr₁ hk₁ hq₁ n₁ kf₁ kg₁ hres₁ hdef₁ hprog₁ hact₁)
    (replaceBranch m hF hL pre tail p hlist q₂ hg tr₂ hk₂ hq₂ n₂ kf₂ kg₂ hres₂ hdef₂ hprog₂ hact₂)
    (replaceBranch_phi_lt m hF hL pre tail p hlist q₁ hg tr₁ hk₁ hq₁ n₁ kf₁ kg₁ hres₁ hdef₁ hprog₁ hact₁)
    (replaceBranch_phi_lt m hF hL pre tail p hlist q₂ hg tr₂ hk₂ hq₂ n₂ kf₂ kg₂ hres₂ hdef₂ hprog₂ hact₂) (by
    rw [forest_value_eq F pre tail p hlist]
    unfold ForestBranch.term
    rw [replaceBranch_value m hF hL pre tail p hlist q₁ hg tr₁ hk₁ hq₁ n₁ kf₁ kg₁ hres₁ hdef₁ hprog₁ hact₁,
      replaceBranch_value m hF hL pre tail p hlist q₂ hg tr₂ hk₂ hq₂ n₂ kf₂ kg₂ hres₂ hdef₂ hprog₂ hact₂]
    have h1 : I₁*q₁.value γ δ C1 ≤ N^n₁*KF^kf₁*KG^kg₁*q₁.value γ δ C1 := by gcongr
    have h2 : I₂*q₂.value γ δ C1 ≤ N^n₂*KF^kf₂*KG^kg₂*q₂.value γ δ C1 := by gcongr
    calc _ ≤ (pre.map fun p => p.value γ δ C1).prod*(I₁*q₁.value γ δ C1+I₂*q₂.value γ δ C1)*
          (tail.map fun p => p.value γ δ C1).prod := by gcongr
      _ ≤ (pre.map fun p => p.value γ δ C1).prod*
            (N^n₁*KF^kf₁*KG^kg₁*q₁.value γ δ C1+N^n₂*KF^kf₂*KG^kg₂*q₂.value γ δ C1)*
          (tail.map fun p => p.value γ δ C1).prod := by gcongr
      _ = _ := by dsimp only [replaceBranch]; ring)

end WaveTurbulence.Mole.AppbAlgorithm
