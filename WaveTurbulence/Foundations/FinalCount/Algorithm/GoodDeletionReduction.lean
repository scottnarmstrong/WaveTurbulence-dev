/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD34Good
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS32Good
public import WaveTurbulence.Foundations.FinalCount.AppBHalfGap
import Mathlib.Tactic

/-! # Complete good deletion reductions for source rules four and five -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v

structure GoodDeletionReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (k : AppbPatternKind) (r : AppbRealization M k.pattern)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  labels : Fin k.pattern.edges.length → (Fin d → ℤ)
  step : GeometricStep (ofMolecule M) (ofMolecule r.post)
  invariants : DeletionPostInvariants r L (L^(-γ+η)/2) w A P labels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A labels) P)
    (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))

private noncomputable def goodDeletionOfDeviation {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (k : AppbPatternKind) (r : AppbRealization M k.pattern)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (q : Fin k.pattern.edges.length → (Fin d → ℤ))
    (hM : M.IsMolecule) (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (hLG : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2))
    (hq : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
      (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A q) P)
      (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))) : GoodDeletionReduction M k r L γ δ η C1 w A P where
  labels := q
  step := .delete (ofMolecule M) k r
  invariants := deletionPostInvariants r L (L^(-γ+η)/2) w A P q hM hno hnt hLG
  deviation := hq

/-- DH23 3D4-G, all four actual figure layouts, with a complete concrete
post problem and carrier-uniform threshold. -/
theorem exists_d34_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D) (k : AppbPatternKind),k ∈ appbD34Kinds →
    ∀ r : AppbRealization M k.pattern,M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_d34_good_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hno hnt hconn hb w A P hP hLG
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L hL M k hk r hM hconn hb w A P hP
  exact ⟨goodDeletionOfDeviation M k r L γ δ η C1 w A P q hM hno hnt hLG hq⟩

/-- DH23 3S2-G, all four actual figure layouts, under the iterated
half-gap standing premise, with no loss in the good exponent. -/
theorem exists_s32_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D) (k : AppbPatternKind),k ∈ appbS32Kinds →
    ∀ r : AppbRealization M k.pattern,M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (GoodDeletionReduction M k r L γ δ η C1 w A P) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hη,hηγ]
  intro δ hδ
  obtain ⟨Lb,hbase⟩ := uniform_s32_good_bound d hd γ hγ (2*η/3) hη' hηγ' δ hδ
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD C1 hC1 L hL M k hk r hM hno hnt hconn hb w A P hP hLG
  have hLG' : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) :=
    fun κ hκ => (hLG κ hκ).mono (hh L ((le_max_right Lb Lh).trans hL))
  obtain ⟨q,hq⟩ := hbase V D C1 hC1 L ((le_max_left Lb Lh).trans hL) M k hk r hM hconn hb w A P hP hLG'
  exact ⟨goodDeletionOfDeviation M k r L γ δ η C1 w A P q hM hno hnt hLG hq⟩

end WaveTurbulence.Mole.AppbAlgorithm
