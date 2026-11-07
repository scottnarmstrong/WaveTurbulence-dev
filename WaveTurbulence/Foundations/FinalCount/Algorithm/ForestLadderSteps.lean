/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestCaseSteps
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestLadder
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ZeroNormalResource
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33LabelReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33NormalReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33CommonTailReduction
import Mathlib.Tactic

/-! # Ladder-continuing branches (rule three(b))

The continuing 3D3-1N / 3D3-2G pair stays in the ladder mode at the
post component, with the next displayed head chosen by the proved
`LadderHead.afterContinuing`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- A branch whose mode continues a ladder at the replaced component. -/
noncomputable def replaceBranchLadder (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state)
    (hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b)
    (head : LadderHead q.state) (n kf kg : ℕ)
    (hres : forestPot F+forestSlack F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤
      forestBalancedPotential (pre.map Problem.state++q.state::tail.map Problem.state)+
      (if q.state.graph.deg (head.figure.vertex 3) = 4 ∧ q.state.graph.deg (head.figure.vertex 4) = 4
        then 0 else 16000))
    (hdef : kg = 0 → defectPotential p.state.graph ≤ defectPotential q.state.graph)
    (hprog : n+kf+kg = 0 → p.state.graph.bonds.Nonempty → q.state.graph.bonds.Nonempty)
    (hact : stateAct p.state ≤ stateAct q.state+60*((n : ℤ)+kf+kg)) :
    ForestBr m F :=
  have hGg := F.replaceLadder_graphs pre tail p hlist q tr hk0 hL.le hg head
  have hGok : ForestOk m (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head) := by
    constructor
    · intro p' hp'
      have hs : p'.state ∈ (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs :=
        List.mem_map_of_mem hp'
      rw [hGg] at hs
      rcases List.mem_append.mp hs with h | h
      · obtain ⟨p'',hp'',e⟩ := List.mem_map.mp h
        rw [← e]
        exact graphOk_of_forestOk hF _ (List.mem_map_of_mem (hlist ▸ List.mem_append_left _ hp''))
      · rcases List.mem_cons.mp h with e | h
        · rw [e]; exact hq
        · obtain ⟨p'',hp'',e⟩ := List.mem_map.mp h
          rw [← e]
          exact graphOk_of_forestOk hF _
            (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp'')))
    · change ∀ q' ∈ (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).problems,
        ∀ a ∈ q'.state.graph.atoms,∀ b ∈ q'.state.graph.atoms,q'.state.graph.SameComponent a b
      intro q' hq'
      have hs : q'.state ∈ (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs :=
        List.mem_map_of_mem hq'
      rw [hGg] at hs
      rcases List.mem_append.mp hs with h | h
      · obtain ⟨p'',hp'',e⟩ := List.mem_map.mp h
        rw [← e]
        exact hconnF _ (List.mem_map_of_mem (hlist ▸ List.mem_append_left _ hp''))
      · rcases List.mem_cons.mp h with e | h
        · rw [e]; exact head.connected
        · obtain ⟨p'',hp'',e⟩ := List.mem_map.mp h
          rw [← e]
          exact hconnF _
            (List.mem_map_of_mem (hlist ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hp'')))
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  have hphi : forestPhi (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head)+1 ≤ forestPhi F := by
    unfold forestPhi
    rw [hGg,hFg]
    exact forestBonds_trace_decrease _ _ tr hk0
  ⟨F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head,n,kf,kg,
    F.replaceLadder_weight_lt pre tail p hlist q tr hk0 hL.le hg head,hGok,by
    have e : forestSlack (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head) =
        (if q.state.graph.deg (head.figure.vertex 3) = 4 ∧ q.state.graph.deg (head.figure.vertex 4) = 4
          then 0 else 16000) := rfl
    change _ ≤ forestBalancedPotential (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs+
      forestSlack (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head)
    rw [hGg,e]
    exact hres,
    fun h0 => by
      have h1 := forestDefect_edit (pre.map Problem.state) (tail.map Problem.state) p.state q.state
      change forestDefectPotential F.graphs ≤
        forestDefectPotential (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs
      rw [hGg,hFg]
      linarith only [h1,hdef h0],
    fun hb => by
      by_cases hz : n+kf+kg = 0
      · right
        change ListBonds (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs
        rw [hGg]
        exact listBonds_edit (hprog hz) (hFg ▸ hb)
      · exact Or.inl (Nat.pos_of_ne_zero hz),
    by omega,
    forestAct_replace pre tail p hlist q.state hGg hact⟩

theorem replaceBranchLadder_phi_lt (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) hconnF (head : LadderHead q.state) (n kf kg : ℕ) hres hdef hprog hact :
    forestPhi (replaceBranchLadder m hF hL pre tail p hlist q hg tr hk0 hq hconnF head n kf kg hres hdef hprog hact).G <
      forestPhi F := by
  have hGg := F.replaceLadder_graphs pre tail p hlist q tr hk0 hL.le hg head
  have hFg : F.graphs = pre.map Problem.state++p.state::tail.map Problem.state := by
    simp [CountingForest.graphs,hlist]
  change forestBonds (F.replaceLadder pre tail p hlist q tr hk0 hL.le hg head).graphs < forestBonds F.graphs
  rw [hGg,hFg]
  have := forestBonds_trace_decrease (pre.map Problem.state) (tail.map Problem.state) tr hk0
  omega

theorem replaceBranchLadder_value (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q : Problem.{u,v} V d L w c g0)
    (hg : F.gap-L^(-γ) ≤ g0) {k0 : ℕ} (tr : Trace p.state q.state k0) (hk0 : 0 < k0)
    (hq : GraphOk L m q.state) hconnF (head : LadderHead q.state) (n kf kg : ℕ) hres hdef hprog hact (δ C1 : ℝ) :
    (replaceBranchLadder m hF hL pre tail p hlist q hg tr hk0 hq hconnF head n kf kg hres hdef hprog hact).G.value δ C1 =
      (pre.map fun p => p.value γ δ C1).prod*q.value γ δ C1*(tail.map fun p => p.value γ δ C1).prod :=
  F.replaceLadder_value pre tail p hlist q tr hk0 hL.le hg head δ C1

/-- Two branches given with their value identities. -/
noncomputable def forestTwoOfBranches (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {g0 : ℝ} (q₁ q₂ : Problem.{u,v} V d L w c g0)
    (b₁ b₂ : ForestBr m F) (δ C1 : ℝ)
    (hv₁ : b₁.G.value δ C1 = (pre.map fun p => p.value γ δ C1).prod*q₁.value γ δ C1*
      (tail.map fun p => p.value γ δ C1).prod)
    (hv₂ : b₂.G.value δ C1 = (pre.map fun p => p.value γ δ C1).prod*q₂.value γ δ C1*
      (tail.map fun p => p.value γ δ C1).prod)
    (N KF KG : ℝ≥0∞) (I₁ I₂ : ℝ≥0∞) (hI₁ : I₁ ≤ N^b₁.n*KF^b₁.kf*KG^b₁.kg)
    (hI₂ : I₂ ≤ N^b₂.n*KF^b₂.kf*KG^b₂.kg)
    (hs₁ : forestPhi b₁.G < forestPhi F) (hs₂ : forestPhi b₂.G < forestPhi F)
    (hloc : p.value γ δ C1 ≤ I₁*q₁.value γ δ C1+I₂*q₂.value γ δ C1) :
    ForestStep m F N KF KG δ C1 :=
  .two b₁ b₂ hs₁ hs₂ (by
    rw [forest_value_eq F pre tail p hlist]
    unfold ForestBranch.term
    rw [hv₁,hv₂]
    have h1 : I₁*q₁.value γ δ C1 ≤ N^b₁.n*KF^b₁.kf*KG^b₁.kg*q₁.value γ δ C1 := by gcongr
    have h2 : I₂*q₂.value γ δ C1 ≤ N^b₂.n*KF^b₂.kf*KG^b₂.kg*q₂.value γ δ C1 := by gcongr
    calc _ ≤ (pre.map fun p => p.value γ δ C1).prod*(I₁*q₁.value γ δ C1+I₂*q₂.value γ δ C1)*
          (tail.map fun p => p.value γ δ C1).prod := by gcongr
      _ ≤ (pre.map fun p => p.value γ δ C1).prod*
            (N^b₁.n*KF^b₁.kf*KG^b₁.kg*q₁.value γ δ C1+N^b₂.n*KF^b₂.kf*KG^b₂.kg*q₂.value γ δ C1)*
          (tail.map fun p => p.value γ δ C1).prod := by gcongr
      _ = _ := by ring)

theorem forestPot_edit_eq {F : CountingForest.{u,v} V d L γ η w c B}
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (t : State.{u,v} V) :
    forestBalancedPotential (pre.map Problem.state++t::tail.map Problem.state) =
      forestPot F+(balancedPotential t.graph-balancedPotential p.state.graph) := by
  have h2 := forestBalancedPotential_edit (pre.map Problem.state) (tail.map Problem.state) p.state t
  have h3 : forestPot F = forestBalancedPotential (pre.map Problem.state++p.state::tail.map Problem.state) := by
    unfold forestPot; congr 1; simp [CountingForest.graphs,hlist]
  rw [h3]; linarith only [h2]

/-- Rule three(b): the continuing normal/good label pair. Both outputs stay
in the ladder mode at the next displayed head. -/
theorem exists_continuing_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 gp : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.d33.pattern)
    (ho : AppbD33BoundaryOpposite p.state.graph r) (hc : D33Continues r)
    (hb : ∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e)
    (hconnp : ∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b)
    (hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b)
    (lr : D33LabelReduction p.state.graph r L γ δ C1 gp w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  let zd : ZeroNormalData p.state :=
    { figure := r, opposite := ho, noBridges := hb, connected := hconnp, stage := .continuing hc }
  let head' : LadderHead (ofMolecule r.post) := LadderHead.afterContinuing r hconnp hb hc
  let pa := p.withAdm (fun κ => p.admissible κ ∧ AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ)
    (fun _ h => h.1)
  let pb := p.withAdm (fun κ => p.admissible κ ∧ ¬AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ)
    (fun _ h => h.1)
  let q₁ := pa.deletion r lr.normalLabels
  let q₂ := pb.deletion r lr.goodLabels
  have tr : Trace p.state (ofMolecule r.post) (0+1) := Trace.cons lr.step.geometric (Trace.nil _)
  have hq₁ : GraphOk L m q₁.state := graphOk_deletion pa hpOk r _
  have hq₂ : GraphOk L m q₂.state := graphOk_deletion pb hpOk r _
  have hg1 : F.gap-L^(-γ) ≤ F.gap := gap_step_le hL γ _
  have hpe := forestPot_edit_eq pre tail p hlist (ofMolecule r.post)
  have hdrop := zd.balanced_drop_le p.molecule
  have hsl := forestSlack_le F
  have hno := p.noLoops
  have e1 : q₁.state = ofMolecule r.post := rfl
  have e2 : q₂.state = ofMolecule r.post := rfl
  let hd₁ : LadderHead q₁.state := head'
  let hd₂ : LadderHead q₂.state := head'
  have hnn : zd.regularNext → balancedPotential p.state.graph ≤ balancedPotential (ofMolecule r.post).graph :=
    fun h => zd.balanced_nondecrease hno h
  have hres₁ : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) ≤
      forestBalancedPotential (pre.map Problem.state++q₁.state::tail.map Problem.state)+
      (if q₁.state.graph.deg (hd₁.figure.vertex 3) = 4 ∧ q₁.state.graph.deg (hd₁.figure.vertex 4) = 4
        then 0 else 16000) := by
    have key : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) ≤
        (forestPot F+(balancedPotential r.post-balancedPotential p.state.graph))+
        (if r.post.deg (head'.figure.vertex 3) = 4 ∧ r.post.deg (head'.figure.vertex 4) = 4
          then 0 else 16000) := by
      by_cases hreg : zd.regularNext
      · have h1 := hnn hreg
        have h2 : r.post.deg (head'.figure.vertex 3) = 4 ∧ r.post.deg (head'.figure.vertex 4) = 4 := hreg
        rw [if_pos h2]
        simp only [Nat.cast_zero,mul_zero,add_zero]
        have h1' : balancedPotential p.state.graph ≤ balancedPotential r.post := h1
        linarith only [h1',hSl]
      · have h2 : ¬(r.post.deg (head'.figure.vertex 3) = 4 ∧ r.post.deg (head'.figure.vertex 4) = 4) := hreg
        rw [if_neg h2]
        simp only [Nat.cast_zero,mul_zero,add_zero]
        have h4 : balancedPotential p.state.graph-16000 ≤ balancedPotential r.post := hdrop
        linarith only [h4,hSl]
    have hpe' : forestBalancedPotential (pre.map Problem.state++q₁.state::tail.map Problem.state) =
        forestPot F+(balancedPotential r.post-balancedPotential p.state.graph) := hpe
    rw [hpe']
    exact key
  have hres₂ : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((1 : ℕ) : ℤ)) ≤
      forestBalancedPotential (pre.map Problem.state++q₂.state::tail.map Problem.state)+
      (if q₂.state.graph.deg (hd₂.figure.vertex 3) = 4 ∧ q₂.state.graph.deg (hd₂.figure.vertex 4) = 4
        then 0 else 16000) := by
    have key : forestPot F+forestSlack F+2*((0 : ℕ) : ℤ)-48000*(((0 : ℕ) : ℤ)+((1 : ℕ) : ℤ)) ≤
        (forestPot F+(balancedPotential r.post-balancedPotential p.state.graph))+
        (if r.post.deg (head'.figure.vertex 3) = 4 ∧ r.post.deg (head'.figure.vertex 4) = 4
          then 0 else 16000) := by
      have h4 : balancedPotential p.state.graph-16000 ≤ balancedPotential r.post := hdrop
      split_ifs <;> simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,zero_add] <;> linarith only [h4,hsl]
    have hpe' : forestBalancedPotential (pre.map Problem.state++q₂.state::tail.map Problem.state) =
        forestPot F+(balancedPotential r.post-balancedPotential p.state.graph) := hpe
    rw [hpe']
    exact key
  have hdef₁ : (0 : ℕ) = 0 → defectPotential p.state.graph ≤ defectPotential q₁.state.graph :=
    fun _ => lr.step.defect_mono
  have hprog₁ : 0+0+0 = 0 → p.state.graph.bonds.Nonempty → q₁.state.graph.bonds.Nonempty :=
    fun _ _ => realization_bonds_nonempty head'.figure
  have hdef₂ : (1 : ℕ) = 0 → defectPotential p.state.graph ≤ defectPotential q₂.state.graph :=
    fun h => absurd h (by norm_num)
  have hprog₂ : 0+0+1 = 0 → p.state.graph.bonds.Nonempty → q₂.state.graph.bonds.Nonempty :=
    fun h => absurd h (by norm_num)
  have hact₀ : stateAct p.state ≤ stateAct (ofMolecule r.post) := by
    have hh := zd.active_change p.molecule hno
    have hz : zd.charge = 0 := rfl
    rw [hz] at hh
    refine stateAct_le_of_noloss ?_ (pendingSlack_of_pair _ (d33_realization_has_pair r))
    change activeLinkPotential p.state.graph ≤ activeLinkPotential r.post
    have : activeLinkPotential zd.target.graph = activeLinkPotential r.post := rfl
    omega
  have hact₁ : stateAct p.state ≤ stateAct q₁.state+60*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)) := by
    rw [e1]; push_cast; linarith only [hact₀]
  have hact₂ : stateAct p.state ≤ stateAct q₂.state+60*(((0 : ℕ) : ℤ)+((0 : ℕ) : ℤ)+((1 : ℕ) : ℤ)) := by
    rw [e2]; push_cast; linarith only [hact₀]
  let b₁ := replaceBranchLadder m hF hL pre tail p hlist q₁ hg1 (tr) (Nat.succ_pos 0) hq₁ hconnF hd₁ 0 0 0 hres₁ hdef₁ hprog₁ hact₁
  let b₂ := replaceBranchLadder m hF hL pre tail p hlist q₂ hg1 (tr) (Nat.succ_pos 0) hq₂ hconnF hd₂ 0 0 1 hres₂ hdef₂ hprog₂ hact₂
  exact ⟨forestTwoOfBranches m pre tail p hlist q₁ q₂ b₁ b₂ δ C1
    (replaceBranchLadder_value m hF hL pre tail p hlist q₁ hg1 tr (Nat.succ_pos 0) hq₁ hconnF hd₁ 0 0 0 hres₁ hdef₁ hprog₁ hact₁ δ C1)
    (replaceBranchLadder_value m hF hL pre tail p hlist q₂ hg1 tr (Nat.succ_pos 0) hq₂ hconnF hd₂ 0 0 1 hres₂ hdef₂ hprog₂ hact₂ δ C1)
    N KF KG 1 (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))
    (by simp [b₁,replaceBranchLadder]) (by simpa [b₂,replaceBranchLadder] using hK)
    (replaceBranchLadder_phi_lt m hF hL pre tail p hlist q₁ hg1 tr (Nat.succ_pos 0) hq₁ hconnF hd₁ 0 0 0 hres₁ hdef₁ hprog₁ hact₁)
    (replaceBranchLadder_phi_lt m hF hL pre tail p hlist q₂ hg1 tr (Nat.succ_pos 0) hq₂ hconnF hd₂ 0 0 1 hres₂ hdef₂ hprog₂ hact₂)
    (by rw [one_mul]; exact lr.bound)⟩

/-- Rule three(c-iii): the terminal normal rung, no controlled factor. -/
noncomputable def forestOfTerminalRung (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L) (hSl : forestSlack F = 0)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 gp : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.d33.pattern)
    (hb : ∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e)
    (hd : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
      a ∉ AppbPatternKind.d33.pattern.removed → p.state.graph.deg (r.vertex a) = 4)
    (hreg : ∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent (r.vertex 1) b →
      b ∉ r.removedAtoms → p.state.graph.deg b = 4)
    (hn : ¬HasD33New r) (hnext : r.post.bonds.Nonempty) (hnopair : ¬HasDegreeThreePair r.post 2)
    (nr : D33NormalReduction p.state.graph r L γ δ C1 gp w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hN : 1 ≤ N) :
    ForestStep m F N KF KG δ C1 :=
  forestOneOfDeletion m hF hL pre tail p hlist hp r nr.labels nr.step.geometric
    (BalancedStep.terminalRung p.state r p.noLoops hb hd hreg (by
      rintro ⟨q,h1,h2,h3,h4⟩
      exact hn ⟨q,h1,h2,h3,h4⟩)) 0 0 0
    (by rw [hSl]; simp) (fun _ => nr.step.defect_mono) (fun _ _ => hnext)
    (by
      have h20 := nr.step.geometric.activePotential_drop_le p.molecule
        (appb_eraseAtoms_isMolecule p.state.graph p.molecule r.removedAtoms)
      simpa using stateAct_le_of_terminal_rung (s := p.state) (t := ofMolecule r.post)
        (by change activeLinkPotential p.state.graph ≤ activeLinkPotential r.post+20
            change activeLinkPotential p.state.graph-20 ≤ activeLinkPotential r.post at h20
            omega)
        (pendingSlack_of_pair _ (d33_realization_has_pair r)) hnext hnopair)
    N KF KG δ C1 1 (by simp) nr.deviation

/-- Rule three(c-i): the common-tail pair (normal head, good tail) is one
compound step with one controlled factor. -/
theorem exists_common_tail_step (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems) (δ C1 : ℝ)
    (r : AppbRealization p.state.graph AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33same.pattern)
    (ct : D33CommonTailReduction p.state.graph r t L γ δ η C1 w p.admissible p.scales)
    (N KF KG : ℝ≥0∞) (hK : ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ KG) :
    Nonempty (ForestStep m F N KF KG δ C1) := by
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  let q₁ := p.deletion r ct.headLabels
  let q₂ := q₁.deletion t ct.tailLabels
  have tr : Trace p.state q₂.state (0+1+1) :=
    Trace.cons ct.headStep.geometric (Trace.cons ct.tailStep (Trace.nil _))
  have hsl := forestSlack_le F
  have hb1 := (BalancedStep.delete p.state .d33 r p.molecule).potential_bound
  have hb2 := (BalancedStep.delete q₁.state .d33same t q₁.molecule).potential_bound
  have hpe : forestBalancedPotential (pre.map Problem.state++ofMolecule r.post::tail.map Problem.state) =
      forestPot F+(balancedPotential r.post-balancedPotential p.state.graph) :=
    forestPot_edit_eq pre tail p hlist (ofMolecule r.post)
  have hed : forestBalancedPotential (pre.map Problem.state++ofMolecule t.post::tail.map Problem.state)-
      forestBalancedPotential (pre.map Problem.state++ofMolecule r.post::tail.map Problem.state) =
        balancedPotential t.post-balancedPotential r.post :=
    forestBalancedPotential_edit (pre.map Problem.state) (tail.map Problem.state)
      (ofMolecule r.post) (ofMolecule t.post)
  have hpe2 : forestBalancedPotential (pre.map Problem.state++q₂.state::tail.map Problem.state) =
      forestPot F+(balancedPotential r.post-balancedPotential p.state.graph)+
        (balancedPotential t.post-balancedPotential r.post) := by
    have : forestBalancedPotential (pre.map Problem.state++(ofMolecule t.post)::tail.map Problem.state) =
        forestBalancedPotential (pre.map Problem.state++(ofMolecule r.post)::tail.map Problem.state)+
          (balancedPotential t.post-balancedPotential r.post) := by
      have := hed; linarith only [this]
    exact this.trans (by rw [hpe])
  refine ⟨forestOneOfReplace m hF hL pre tail p hlist q₂ (gap_step_le hL γ _) tr (Nat.succ_pos _)
    (graphOk_of_trace hpOk tr (appb_eraseAtoms_noTripleBonds r.post t.removedAtoms
      (appb_eraseAtoms_noTripleBonds p.state.graph r.removedAtoms hpOk.1))) 0 0 1
    (by
      rw [hpe2]
      have h1 : balancedPotential p.state.graph-16000 ≤ balancedPotential r.post := by
        have h := hb1
        simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,add_zero] at h
        exact h
      have h2 : balancedPotential r.post-16000 ≤ balancedPotential t.post := by
        have h := hb2
        simp only [Nat.cast_zero,mul_zero,Nat.cast_one,mul_one,add_zero] at h
        exact h
      push_cast
      linarith only [h1,h2,hsl])
    (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    (by
      have h1 : stateAct p.state ≤ stateAct q₂.state+60 :=
        stateAct_le_two ct.headStep.geometric ct.tailStep p.molecule q₁.molecule q₂.molecule
      push_cast; linarith only [h1])
    N KF KG δ C1 (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) (by simpa using hK)
    ct.deviation⟩

end WaveTurbulence.Mole.AppbAlgorithm
