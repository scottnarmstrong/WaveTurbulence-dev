/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceGroupedNorm
public import WaveTurbulence.Foundations.Sumint.SourceFactorRegularity
public import WaveTurbulence.Foundations.Sumint.SourceGainGeometry

/-!
# Pair factors retaining exactly the needed case-(a) restriction

All other static constraints can be discarded for the nonnegative bound.
The first case-(a) pair keeps its middle-time strip; the checked physical
pair estimate is uniform in that distinguished linear time.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- The first pair of a case-(a) source block. -/
@[expose] def caseAPair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Prop :=
  D.S.nor a.1 = false ∧ D.badKind a.1 = 0 ∧ (a.2:ℕ) = 0

/-- The local pair norm with its gap amplitude and, in case (a), its middle-time strip. -/
@[expose] noncomputable def orderedPairNorm {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) : ℝ :=
  if caseAPair D a then
    if |z.1-u a.1| ≤ |z.1-z.2| then
      pairGapAmplitude D η a z*‖pairTimeSum D L γ δ p ν r t a z‖ else 0
  else pairGapAmplitude D η a z*‖pairTimeSum D L γ δ p ν r t a z‖

/-- The exact static source constraints imply the retained restriction at every case-(a) pair. -/
theorem source_case_a_pair_strip {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (τ : D.S.TVar → ℝ) (hτ : τ ∈ staticTimeDomain D)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a) :
    |τ (.inl ⟨a.1,a.2.succ⟩)-τ (.inl ⟨a.1,0⟩)| ≤
      |τ (.inl ⟨a.1,a.2.succ⟩)-τ (.inr (.inl a))| := by
  rcases a with ⟨i,j⟩
  obtain ⟨hm,hs⟩ := source_case_a_strip D hD i ha.1 ha.2.1 τ hτ
  have hj : j = (⟨0,hm⟩ : Fin (D.S.m i)) := Fin.ext ha.2.2
  rw [hj]
  exact hs

/-- On the original static domain the ordered pair equals the literal unrestricted pair norm. -/
theorem orderedPairNorm_eq_on_static {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) (hτ : τ ∈ staticTimeDomain D)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    orderedPairNorm D L γ δ η p ν r t
      (fun i => τ (.inl ⟨i,0⟩)) a (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a))) =
      pairGapAmplitude D η a (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a))) *
        ‖pairTimeSum D L γ δ p ν r t a (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a)))‖ := by
  unfold orderedPairNorm
  by_cases ha : caseAPair D a
  · rw [ite_eq_left ha,ite_eq_left (source_case_a_pair_strip D hD τ hτ a ha)]
  · rw [ite_eq_right ha]

/-- The pair gap amplitude is measurable in the actual pair-time tuple. -/
theorem measurable_pairGapAmplitude {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : Measurable (pairGapAmplitude D η a) := by
  classical
  unfold pairGapAmplitude
  split_ifs <;> fun_prop

/-- The actual pair-time norm is measurable jointly in its outer and inner times. -/
theorem measurable_pairTimeSum_norm {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    Measurable (fun z : ℝ × ℝ => ‖pairTimeSum D L γ δ p ν r t a z‖) := by
  have hv : Measurable (fun z : ℝ × ℝ => ![z.1,z.2]) := by fun_prop
  have hm := (measurable_plainTimeNormFactor D hL γ δ p ν r t (.inr (.inl a))).comp hv
  change Measurable (fun z : ℝ × ℝ =>
    ‖pairTimeSum D L γ δ p ν r t a ((![z.1,z.2]) 0,(![z.1,z.2]) 1)‖) at hm
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using hm

end WaveTurbulence.Sumint
