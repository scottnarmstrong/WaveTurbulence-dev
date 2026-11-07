/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestMoveBranches
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedTrace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.AdmissibilityPartition
import Mathlib.Tactic

/-! # Forest step data for literal deletions of a source figure

The post problem is `Problem.deletion`: its graph is the literal
figure deletion, its admissibility is the conditioned post predicate, and
every standing invariant is derived from the pre problem. The count
deviation and the balanced step are inputs from the source operation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c g : ℝ} {w : Mom d} {B : ℕ}

/-- The same graph and scales with a sub-admissibility predicate. -/
def Problem.withAdm (p : Problem.{u,v} V d L w c g)
    (A' : (p.state.Dart → (Fin d → ℤ)) → Prop) (h : ∀ κ,A' κ → p.admissible κ) :
    Problem.{u,v} V d L w c g where
  state := p.state
  admissible := A'
  scales := p.scales
  molecule := p.molecule
  noLoops := p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := p.validLinkScales.mono h
  mateLabels := fun κ hκ => p.mateLabels κ (h κ hκ)
  largeGap := fun κ hκ => p.largeGap κ (h κ hκ)

theorem gap_step_le' (hL : 0 < L) (γ g : ℝ) : g-L^(-γ) ≤ g := by
  have := Real.rpow_nonneg hL.le (-γ); linarith only [this]

theorem forestBalancedPotential_edit (pre tail : List (State.{u,v} V)) (s t : State.{u,v} V) :
    forestBalancedPotential (pre++t::tail)-forestBalancedPotential (pre++s::tail) =
      balancedPotential t.graph-balancedPotential s.graph := by
  simp only [forestBalancedPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  ring

theorem forestPot_edit_bound {F : CountingForest.{u,v} V d L γ η w c B}
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) {t : State.{u,v} V} {n0 k0 : ℕ}
    (bs : BalancedStep p.state t n0 k0) :
    forestPot F+2*(n0 : ℤ)-16000*(k0 : ℤ) ≤
      forestBalancedPotential (pre.map Problem.state++t::tail.map Problem.state) := by
  have h1 := bs.potential_bound
  have h2 := forestBalancedPotential_edit (pre.map Problem.state) (tail.map Problem.state) p.state t
  have h3 : forestPot F = forestBalancedPotential (pre.map Problem.state++p.state::tail.map Problem.state) := by
    unfold forestPot; congr 1; simp [CountingForest.graphs,hlist]
  rw [h3]
  linarith only [h1,h2]

theorem graphOk_deletion {m : ℕ} (p : Problem.{u,v} V d L w c g) (hp : GraphOk L m p.state)
    {P : AppbPattern} (r : AppbRealization p.state.graph P) (q : Fin P.edges.length → (Fin d → ℤ)) :
    GraphOk L m (p.deletion r q).state := by
  refine ⟨p.deletion_noTripleBonds hp.1 r q,?_⟩
  have h := r.post_card_atoms
  have h2 : (r.post.atoms.card : ℝ) ≤ p.state.graph.atoms.card := by exact_mod_cast (by omega)
  exact h2.trans hp.2

/-- A counted deletion step loses at most `60` per count. -/
theorem stateAct_deletion_counted (p : Problem.{u,v} V d L w c g) {P : AppbPattern}
    (r : AppbRealization p.state.graph P) (hs : GeometricStep p.state (ofMolecule r.post))
    (c : ℤ) (hc : 1 ≤ c) : stateAct p.state ≤ stateAct (ofMolecule r.post)+60*c :=
  stateAct_counted hs p.molecule (appb_eraseAtoms_isMolecule p.state.graph p.molecule r.removedAtoms) c hc

/-- One literal deletion step, with the source count deviation `I` and the
accounting increments `(n,k)` justified by a balanced step `(n0,k0)`. -/
noncomputable def forestOneOfDeletion (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems)
    {P : AppbPattern} (r : AppbRealization p.state.graph P) (q : Fin P.edges.length → (Fin d → ℤ))
    (hs : GeometricStep p.state (ofMolecule r.post)) {n0 k0 : ℕ}
    (bs : BalancedStep p.state (ofMolecule r.post) n0 k0) (n kf kg : ℕ)
    (hnum : forestSlack F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤ 2*(n0 : ℤ)-16000*(k0 : ℤ))
    (hdef : kg = 0 → defectPotential p.state.graph ≤ defectPotential r.post)
    (hprog : n+kf+kg = 0 → p.state.graph.bonds.Nonempty → r.post.bonds.Nonempty)
    (hact : stateAct p.state ≤ stateAct (ofMolecule r.post)+60*((n : ℤ)+kf+kg))
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) (I : ℝ≥0∞) (hI : I ≤ N^n*KF^kf*KG^kg)
    (hdev : IsDeviation (appbLinkCountA p.state.graph L γ δ C1 w p.admissible p.scales)
      (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility p.admissible q) p.scales) I) :
    ForestStep m F N KF KG δ C1 :=
  forestOneOfReplace m hF hL pre tail p hlist (p.deletion r q)
    (by have := Real.rpow_nonneg hL.le (-γ); linarith only [this])
    (Trace.cons hs (Trace.nil _)) (Nat.succ_pos 0)
    (graphOk_deletion p (graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)) r q) n kf kg
    (by
      have := forestPot_edit_bound pre tail p hlist bs
      have e : (p.deletion r q).state = ofMolecule r.post := rfl
      rw [e]; linarith only [this,hnum]) hdef hprog hact N KF KG δ C1 I hI hdev

/-- A label test splits one literal deletion into two decorated outcomes
(passing and failing), as in the source rules two(b)-(d) and three(b)-(c). -/
noncomputable def forestTwoOfDeletionLabels (m : ℕ) {F : CountingForest.{u,v} V d L γ η w c B}
    (hF : ForestOk m F) (hL : 0 < L)
    (pre tail : List (Problem.{u,v} V d L w c F.gap)) (p : Problem.{u,v} V d L w c F.gap)
    (hlist : F.problems = pre++p::tail) (hp : p ∈ F.problems)
    (Test : (p.state.Dart → (Fin d → ℤ)) → Prop)
    {P : AppbPattern} (r : AppbRealization p.state.graph P)
    (q₁ q₂ : Fin P.edges.length → (Fin d → ℤ))
    (hs : GeometricStep p.state (ofMolecule r.post)) {n₁' k₁' n₂' k₂' : ℕ}
    (bs₁ : BalancedStep p.state (ofMolecule r.post) n₁' k₁')
    (bs₂ : BalancedStep p.state (ofMolecule r.post) n₂' k₂') (n₁ kf₁ kg₁ n₂ kf₂ kg₂ : ℕ)
    (hnum₁ : forestSlack F+2*(n₁ : ℤ)-48000*((kf₁ : ℤ)+kg₁) ≤ 2*(n₁' : ℤ)-16000*(k₁' : ℤ))
    (hnum₂ : forestSlack F+2*(n₂ : ℤ)-48000*((kf₂ : ℤ)+kg₂) ≤ 2*(n₂' : ℤ)-16000*(k₂' : ℤ))
    (hdef₁ : kg₁ = 0 → defectPotential p.state.graph ≤ defectPotential r.post)
    (hprog₁ : n₁+kf₁+kg₁ = 0 → p.state.graph.bonds.Nonempty → r.post.bonds.Nonempty)
    (hact₁ : stateAct p.state ≤ stateAct (ofMolecule r.post)+60*((n₁ : ℤ)+kf₁+kg₁))
    (hdef₂ : kg₂ = 0 → defectPotential p.state.graph ≤ defectPotential r.post)
    (hprog₂ : n₂+kf₂+kg₂ = 0 → p.state.graph.bonds.Nonempty → r.post.bonds.Nonempty)
    (hact₂ : stateAct p.state ≤ stateAct (ofMolecule r.post)+60*((n₂ : ℤ)+kf₂+kg₂))
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) (I₁ I₂ : ℝ≥0∞) (hI₁ : I₁ ≤ N^n₁*KF^kf₁*KG^kg₁)
    (hI₂ : I₂ ≤ N^n₂*KF^kf₂*KG^kg₂)
    (hdev₁ : IsDeviation
      (appbLinkCountA p.state.graph L γ δ C1 w (fun κ => p.admissible κ ∧ Test κ) p.scales)
      (appbLinkCountA r.post L γ δ C1 w
        (r.conditionedPostAdmissibility (fun κ => p.admissible κ ∧ Test κ) q₁) p.scales) I₁)
    (hdev₂ : IsDeviation
      (appbLinkCountA p.state.graph L γ δ C1 w (fun κ => p.admissible κ ∧ ¬Test κ) p.scales)
      (appbLinkCountA r.post L γ δ C1 w
        (r.conditionedPostAdmissibility (fun κ => p.admissible κ ∧ ¬Test κ) q₂) p.scales) I₂) :
    ForestStep m F N KF KG δ C1 :=
  let pa := p.withAdm (fun κ => p.admissible κ ∧ Test κ) (fun _ h => h.1)
  let pb := p.withAdm (fun κ => p.admissible κ ∧ ¬Test κ) (fun _ h => h.1)
  have hpOk := graphOk_of_forestOk hF _ (List.mem_map_of_mem hp)
  have tr : ∀ t : State.{u,v} V,GeometricStep p.state t → Trace p.state t (0+1) :=
    fun t h => Trace.cons h (Trace.nil _)
  forestTwoOfReplace m hF hL pre tail p hlist (pa.deletion r q₁) (pb.deletion r q₂)
    (gap_step_le' hL γ _) (tr _ hs) (Nat.succ_pos 0) (tr _ hs) (Nat.succ_pos 0)
    (graphOk_deletion pa hpOk r q₁) (graphOk_deletion pb hpOk r q₂) n₁ kf₁ kg₁ n₂ kf₂ kg₂
    (by
      have := forestPot_edit_bound pre tail p hlist bs₁
      have e : (pa.deletion r q₁).state = ofMolecule r.post := rfl
      rw [e]; linarith only [this,hnum₁])
    (by
      have := forestPot_edit_bound pre tail p hlist bs₂
      have e : (pb.deletion r q₂).state = ofMolecule r.post := rfl
      rw [e]; linarith only [this,hnum₂])
    hdef₁ hprog₁ hact₁ hdef₂ hprog₂ hact₂ N KF KG δ C1 I₁ I₂ hI₁ hI₂
    ((linkCountA_le_test_partition p.state.graph L γ δ C1 w p.admissible Test p.scales).trans
      (add_le_add hdev₁ hdev₂))

end WaveTurbulence.Mole.AppbAlgorithm
