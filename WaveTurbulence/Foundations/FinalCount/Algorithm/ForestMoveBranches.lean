/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestBranches
import Mathlib.Tactic

/-! # Step data for component splitting and discarding terminal components -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

theorem split_graphs (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S) :
    (F.split pre tail p hlist S hS).graphs =
      pre.map Problem.state++(p.side S hS).state::
        (p.side (p.state.graph.atoms \ S) hS.complement).state::tail.map Problem.state := by
  simp [CountingForest.graphs,CountingForest.split]

theorem discard_graphs (F : CountingForest.{u,v} V d L γ η w c B)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (ht : Terminal p.state) :
    (F.discard pre tail p hlist ht).graphs = pre.map Problem.state++tail.map Problem.state := by
  simp [CountingForest.graphs,CountingForest.discard]

noncomputable def forestSplitStep (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hSl : forestSlack F = 0) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (S : Finset V) (hS : AppbClosedSide p.state.graph S)
    (hn : S.Nonempty) (hc : (p.state.graph.atoms \ S).Nonempty)
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) (hδ : 0 < δ) (hC : 0 < C1) :
    ForestStep m F N KF KG δ C1 := by
  have hGg := split_graphs F pre tail p hlist S hS
  have hmode : (F.split pre tail p hlist S hS).mode = .globalScan := rfl
  have hpOk : GraphOk L m p.state := graphOk_of_forestOk hF _
    (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_self)))
  have hGok : ForestOk m (F.split pre tail p hlist S hS) := by
    refine forestOk_of_global m _ hmode ?_
    rw [hGg]
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
      exact graphOk_of_forestOk hF _ (List.mem_map_of_mem (hlist ▸ List.mem_append_left _ hp'))
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨p.side_noTripleBonds hpOk.1 S hS,
          (by exact_mod_cast Finset.card_le_card hS.subset_atoms : ((S.card : ℕ) : ℝ) ≤ _).trans hpOk.2⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨p.side_noTripleBonds hpOk.1 _ hS.complement,
            (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset :
              (((p.state.graph.atoms \ S).card : ℕ) : ℝ) ≤ _).trans hpOk.2⟩
        · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
          exact graphOk_of_forestOk hF _
            (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp')))
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  have hres : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) ≤
      forestPot (F.split pre tail p hlist S hS)+forestSlack (F.split pre tail p hlist S hS) := by
    have hbal := (BalancedForestStep.split (pre.map Problem.state) (tail.map Problem.state) p.state S hS hn hc).potential_bound
    have h0 := forestSlack_global _ hmode
    change _ ≤ forestBalancedPotential (F.split pre tail p hlist S hS).graphs+
      forestSlack (F.split pre tail p hlist S hS)
    rw [hGg,h0]
    have hF' : forestPot F = forestBalancedPotential (pre.map Problem.state++p.state::tail.map Problem.state) := by
      unfold forestPot; congr 1
    rw [hF',hSl]
    have hb3 : forestBalancedPotential (pre.map Problem.state++p.state::tail.map Problem.state) ≤
        forestBalancedPotential (pre.map Problem.state++(p.side S hS).state::
          (p.side (p.state.graph.atoms \ S) hS.complement).state::tail.map Problem.state) := by
      have h := hbal
      simp only [Nat.cast_zero,mul_zero,add_zero,sub_zero] at h
      exact h
    simp only [Nat.cast_zero,mul_zero,add_zero,sub_zero]
    exact hb3
  have hdefF : (0 : ℕ) = 0 → forestDefect F ≤ forestDefect (F.split pre tail p hlist S hS) := by
    intro _
    have h := (NormalFineForestStep.split (pre.map Problem.state) (tail.map Problem.state) p.state S hS hn hc).defect_mono
    change forestDefectPotential F.graphs ≤ forestDefectPotential (F.split pre tail p hlist S hS).graphs
    rw [hGg,hFg]; exact h
  have hprogF : forestHasBonds F → 0 < 0+0+0 ∨ forestHasBonds (F.split pre tail p hlist S hS) := by
    intro hb
    right
    change ListBonds (F.split pre tail p hlist S hS).graphs
    rw [hGg]
    exact listBonds_split p.state S hS (hFg ▸ hb)
  have hphiF : forestPhi (F.split pre tail p hlist S hS) ≤ forestPhi F := by
    have h := (ForestMove.split (pre.map Problem.state) (tail.map Problem.state) p.state S hS hn hc).bonds_le
    unfold forestPhi
    rw [hGg,hFg]; exact h
  have hactF : forestAct F ≤ forestAct (F.split pre tail p hlist S hS)+60*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) := by
    have : stateAct p.state ≤ stateAct (p.side S hS).state+
        stateAct (p.side (p.state.graph.atoms \ S) hS.complement).state := stateAct_split_le p.state S hS
    unfold forestAct
    rw [hGg,hFg]
    simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,Nat.cast_zero]
    simp only [mul_zero,add_zero]
    linarith only [this]
  refine .one ⟨F.split pre tail p hlist S hS,0,0,0,F.split_weight_lt pre tail p hlist S hS hn hc,hGok,hres,hdefF,hprogF,hphiF,hactF⟩ ?_
  simp only [ForestBranch.term,pow_zero,one_mul]
  exact F.value_le_split pre tail p hlist S hS δ C1 hL hδ hC

noncomputable def forestDiscardStep (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (ht : Terminal p.state)
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) :
    ForestStep m F N KF KG δ C1 := by
  have hGg := discard_graphs F pre tail p hlist ht
  have hmode : (F.discard pre tail p hlist ht).mode = .globalScan := rfl
  have hGok : ForestOk m (F.discard pre tail p hlist ht) := by
    refine forestOk_of_global m _ hmode ?_
    rw [hGg]
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
      exact graphOk_of_forestOk hF _ (List.mem_map_of_mem (hlist ▸ List.mem_append_left _ hp'))
    · obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
      exact graphOk_of_forestOk hF _
        (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp')))
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  have hres : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) ≤
      forestPot (F.discard pre tail p hlist ht)+forestSlack (F.discard pre tail p hlist ht) := by
    have hbal := (BalancedForestStep.discard (pre.map Problem.state) (tail.map Problem.state) p.state ht).potential_bound
    have h0 := forestSlack_global _ hmode
    change _ ≤ forestBalancedPotential (F.discard pre tail p hlist ht).graphs+
      forestSlack (F.discard pre tail p hlist ht)
    rw [hGg,h0]
    have hF' : forestPot F = forestBalancedPotential (pre.map Problem.state++p.state::tail.map Problem.state) := by
      unfold forestPot; congr 1
    rw [hF',hSl]
    simp only [Nat.cast_zero,mul_zero,add_zero,sub_zero] at hbal ⊢
    exact hbal
  have hdefF : (0 : ℕ) = 0 → forestDefect F ≤ forestDefect (F.discard pre tail p hlist ht) := by
    intro _
    have h := (NormalFineForestStep.discard (pre.map Problem.state) (tail.map Problem.state) p.state ht).defect_mono
    change forestDefectPotential F.graphs ≤ forestDefectPotential (F.discard pre tail p hlist ht).graphs
    rw [hGg,hFg]; exact h
  have hprogF : forestHasBonds F → 0 < 0+0+0 ∨ forestHasBonds (F.discard pre tail p hlist ht) := by
    intro hb
    right
    change ListBonds (F.discard pre tail p hlist ht).graphs
    rw [hGg]
    exact listBonds_discard ht (hFg ▸ hb)
  have hphiF : forestPhi (F.discard pre tail p hlist ht) ≤ forestPhi F := by
    have h := (ForestMove.discard (pre.map Problem.state) (tail.map Problem.state) p.state ht).bonds_le
    unfold forestPhi
    rw [hGg,hFg]; exact h
  have hactD : forestAct F ≤ forestAct (F.discard pre tail p hlist ht)+60*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) := by
    have := stateAct_terminal ht
    unfold forestAct
    rw [hGg,hFg]
    simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,Nat.cast_zero]
    simp only [mul_zero,add_zero]
    linarith only [this]
  refine .one ⟨F.discard pre tail p hlist ht,0,0,0,F.discard_weight_lt pre tail p hlist ht,hGok,hres,hdefF,hprogF,hphiF,hactD⟩ ?_
  simp only [ForestBranch.term,pow_zero,one_mul]
  exact F.value_le_discard pre tail p hlist ht δ C1

end WaveTurbulence.Mole.AppbAlgorithm
