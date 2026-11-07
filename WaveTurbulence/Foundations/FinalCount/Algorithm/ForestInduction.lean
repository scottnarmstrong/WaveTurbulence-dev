/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForestMove
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedForestTrace
import Mathlib.Tactic

/-! # Well-founded accounting induction over decorated forests

Generic induction behind the Appendix B count: a *step datum* for a forest
is one or two successor forests, each with a normal count `n` and a
controlled (fine/good) count `c`, a strict weight descent, a resource
inequality, and a local value inequality. This file proves only the
induction shell. The scheduler that supplies step data from the actual
priorities is a separate input and nothing here assumes it.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- One successor of a forest with its accounting increments: `n` normal
steps, `kf` fine steps, `kg` good steps. `defect` says that a branch with no
good step does not decrease the defect potential `Dp`, and `progress` that a
forest with bonds either performs a counted step or keeps bonds. -/
structure ForestBranch (Ok : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ)
    (Bd : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Φ : CountingForest.{u,v} V d L γ η w c B → ℕ)
    (F : CountingForest.{u,v} V d L γ η w c B) where
  G : CountingForest.{u,v} V d L γ η w c B
  n : ℕ
  kf : ℕ
  kg : ℕ
  weight_lt : G.weight < F.weight
  ok : Ok G
  resource : Pot F+Sl F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤ Pot G+Sl G
  defect : kg = 0 → Dp F ≤ Dp G
  progress : Bd F → 0 < n+kf+kg ∨ Bd G
  phi : Φ G ≤ Φ F
  act : Ac F ≤ Ac G+60*((n : ℤ)+kf+kg)

/-- Local value bound of a branch: normal factor `N` per normal step, fine
factor `KF` per fine step, good factor `KG` per good step. -/
noncomputable def ForestBranch.term {Ok : CountingForest.{u,v} V d L γ η w c B → Prop}
    {Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ}
    {Bd : CountingForest.{u,v} V d L γ η w c B → Prop}
    {Φ : CountingForest.{u,v} V d L γ η w c B → ℕ}
    {F : CountingForest.{u,v} V d L γ η w c B} (b : ForestBranch Ok Pot Sl Dp Ac Bd Φ F)
    (N KF KG : ℝ≥0∞) (δ C1 : ℝ) : ℝ≥0∞ :=
  N^b.n*KF^b.kf*KG^b.kg*b.G.value δ C1

/-- A single or a two-fold decorated step, with its local value bound. -/
inductive ForestStepData (Ok : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ)
    (Bd : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Φ : CountingForest.{u,v} V d L γ η w c B → ℕ)
    (F : CountingForest.{u,v} V d L γ η w c B) (N KF KG : ℝ≥0∞) (δ C1 : ℝ) : Type _
  | one (b : ForestBranch Ok Pot Sl Dp Ac Bd Φ F) (h : F.value δ C1 ≤ b.term N KF KG δ C1) :
      ForestStepData Ok Pot Sl Dp Ac Bd Φ F N KF KG δ C1
  | two (b₁ b₂ : ForestBranch Ok Pot Sl Dp Ac Bd Φ F) (hs₁ : Φ b₁.G < Φ F) (hs₂ : Φ b₂.G < Φ F)
      (h : F.value δ C1 ≤ b₁.term N KF KG δ C1+b₂.term N KF KG δ C1) :
      ForestStepData Ok Pot Sl Dp Ac Bd Φ F N KF KG δ C1

/-- The accounting conclusion for one forest. -/
def ForestAcct (Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ)
    (Bd : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Φ : CountingForest.{u,v} V d L γ η w c B → ℕ)
    (F : CountingForest.{u,v} V d L γ η w c B) (N KF KG : ℝ≥0∞) (δ C1 : ℝ) : Prop :=
  ∃ n kf kg : ℕ,Pot F+Sl F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤ 0 ∧ (kg = 0 → Dp F ≤ 0) ∧
    (Bd F → 0 < n+kf+kg) ∧ Ac F ≤ 60*((n : ℤ)+kf+kg) ∧ F.value δ C1 ≤ 2^Φ F*N^n*KF^kf*KG^kg

private theorem acct_of_branch {Ok : CountingForest.{u,v} V d L γ η w c B → Prop}
    {Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ}
    {Bd : CountingForest.{u,v} V d L γ η w c B → Prop}
    {Φ : CountingForest.{u,v} V d L γ η w c B → ℕ}
    {F : CountingForest.{u,v} V d L γ η w c B} (b : ForestBranch Ok Pot Sl Dp Ac Bd Φ F)
    {N KF KG : ℝ≥0∞} {δ C1 : ℝ} (hb : ForestAcct Pot Sl Dp Ac Bd Φ b.G N KF KG δ C1) :
    ∃ n kf kg : ℕ,Pot F+Sl F+2*(n : ℤ)-48000*((kf : ℤ)+kg) ≤ 0 ∧ (kg = 0 → Dp F ≤ 0) ∧
      (Bd F → 0 < n+kf+kg) ∧ Ac F ≤ 60*((n : ℤ)+kf+kg) ∧ b.term N KF KG δ C1 ≤ 2^Φ b.G*N^n*KF^kf*KG^kg := by
  obtain ⟨n',kf',kg',hres,hdef,hprog,hact,hval⟩ := hb
  refine ⟨b.n+n',b.kf+kf',b.kg+kg',?_,?_,?_,?_,?_⟩
  · have := b.resource
    push_cast
    linarith only [this,hres]
  · intro h0
    have h1 : b.kg = 0 := by omega
    have h2 : kg' = 0 := by omega
    exact (b.defect h1).trans (hdef h2)
  · intro hF
    rcases b.progress hF with h | h
    · omega
    · have := hprog h; omega
  · have := b.act
    push_cast
    linarith only [this,hact]
  · calc b.term N KF KG δ C1 = N^b.n*KF^b.kf*KG^b.kg*b.G.value δ C1 := rfl
      _ ≤ N^b.n*KF^b.kf*KG^b.kg*(2^Φ b.G*N^n'*KF^kf'*KG^kg') := by gcongr
      _ = 2^Φ b.G*N^(b.n+n')*KF^(b.kf+kf')*KG^(b.kg+kg') := by
          rw [pow_add,pow_add,pow_add]; ring

/-- The generic accounting induction: every admissible forest satisfies
its accounting conclusion, provided every nonempty admissible forest has a
step datum, and the empty forest respects the resource budget. -/
theorem forest_acct_of_steps (Ok : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Pot Sl Dp Ac : CountingForest.{u,v} V d L γ η w c B → ℤ)
    (Bd : CountingForest.{u,v} V d L γ η w c B → Prop)
    (Φ : CountingForest.{u,v} V d L γ η w c B → ℕ) (N KF KG : ℝ≥0∞) (δ C1 : ℝ)
    (hbase : ∀ F,Ok F → F.problems = [] → Pot F+Sl F ≤ 0 ∧ Dp F ≤ 0 ∧ ¬Bd F ∧ Ac F ≤ 0)
    (hstep : ∀ F,Ok F → F.problems ≠ [] →
      Nonempty (ForestStepData Ok Pot Sl Dp Ac Bd Φ F N KF KG δ C1)) :
    ∀ F,Ok F → ForestAcct Pot Sl Dp Ac Bd Φ F N KF KG δ C1 := by
  suffices h : ∀ m : ℕ,∀ F : CountingForest.{u,v} V d L γ η w c B,F.weight = m → Ok F →
      ForestAcct Pot Sl Dp Ac Bd Φ F N KF KG δ C1 from fun F hF => h _ F rfl hF
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro F hm hF
    by_cases hne : F.problems = []
    · obtain ⟨h1,h2,h3,h4⟩ := hbase F hF hne
      refine ⟨0,0,0,?_,fun _ => h2,fun h => absurd h h3,by simpa using h4,?_⟩
      · simpa using h1
      · simp only [CountingForest.value,hne,List.map_nil,List.prod_nil,pow_zero,mul_one]
        exact one_le_pow₀ (by norm_num)
    obtain ⟨S⟩ := hstep F hF hne
    have hrec : ∀ b : ForestBranch Ok Pot Sl Dp Ac Bd Φ F,ForestAcct Pot Sl Dp Ac Bd Φ b.G N KF KG δ C1 :=
      fun b => ih b.G.weight (hm ▸ b.weight_lt) b.G rfl b.ok
    cases S with
    | one b h =>
      obtain ⟨n,kf,kg,hres,hdef,hprog,hact,hval⟩ := acct_of_branch b (hrec b)
      refine ⟨n,kf,kg,hres,hdef,hprog,hact,h.trans (hval.trans ?_)⟩
      have := b.phi
      gcongr
      norm_num
    | two b₁ b₂ hs₁ hs₂ h =>
      obtain ⟨n₁,kf₁,kg₁,hres₁,hdef₁,hprog₁,hact₁,hval₁⟩ := acct_of_branch b₁ (hrec b₁)
      obtain ⟨n₂,kf₂,kg₂,hres₂,hdef₂,hprog₂,hact₂,hval₂⟩ := acct_of_branch b₂ (hrec b₂)
      have hpow : (2 : ℝ≥0∞)^Φ F = 2*2^(Φ F-1) := by
        have : Φ F = (Φ F-1)+1 := by omega
        conv_lhs => rw [this]
        rw [pow_succ]; ring
      have h₁ : (2 : ℝ≥0∞)^Φ b₁.G ≤ 2^(Φ F-1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h₂ : (2 : ℝ≥0∞)^Φ b₂.G ≤ 2^(Φ F-1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hv₁ : b₁.term N KF KG δ C1 ≤ 2^(Φ F-1)*N^n₁*KF^kf₁*KG^kg₁ :=
        hval₁.trans (by gcongr)
      have hv₂ : b₂.term N KF KG δ C1 ≤ 2^(Φ F-1)*N^n₂*KF^kf₂*KG^kg₂ :=
        hval₂.trans (by gcongr)
      rcases le_total (2^(Φ F-1)*N^n₁*KF^kf₁*KG^kg₁) (2^(Φ F-1)*N^n₂*KF^kf₂*KG^kg₂)
        with hle | hle
      · refine ⟨n₂,kf₂,kg₂,hres₂,hdef₂,hprog₂,hact₂,h.trans ?_⟩
        calc _ ≤ 2^(Φ F-1)*N^n₂*KF^kf₂*KG^kg₂+2^(Φ F-1)*N^n₂*KF^kf₂*KG^kg₂ :=
              add_le_add (hv₁.trans hle) hv₂
          _ = 2^Φ F*N^n₂*KF^kf₂*KG^kg₂ := by rw [hpow]; ring
      · refine ⟨n₁,kf₁,kg₁,hres₁,hdef₁,hprog₁,hact₁,h.trans ?_⟩
        calc _ ≤ 2^(Φ F-1)*N^n₁*KF^kf₁*KG^kg₁+2^(Φ F-1)*N^n₁*KF^kf₁*KG^kg₁ :=
              add_le_add hv₁ (hv₂.trans hle)
          _ = 2^Φ F*N^n₁*KF^kf₁*KG^kg₁ := by rw [hpow]; ring

end WaveTurbulence.Mole.AppbAlgorithm
