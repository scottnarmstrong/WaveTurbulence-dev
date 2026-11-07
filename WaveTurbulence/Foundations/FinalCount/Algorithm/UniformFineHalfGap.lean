/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTwoBondFineStrong
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR23FineStrong
public import WaveTurbulence.Foundations.FinalCount.AppBHalfGap
import Mathlib.Tactic

/-! # All fine removals with the iterated half-size large-gap threshold -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

theorem uniform_r2_two_bond_half_gap_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (k : AppbPatternKind),
      k ∈ ([AppbPatternKind.r21,.r22,.r24] : List _) →
      ∀ r : AppbRealization M k.pattern,
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-η/2))) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hηγ,hη]
  obtain ⟨Lb,hb⟩ := uniform_r2_two_bond_fine_strong_bound
    d hd δ γ (2*η/3) C1 hδ hγ hη' hηγ' hC1
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD L hL M k hk r hconn hbridge w Adm hLG scales
  have hg : ∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) := by
    intro κ hκ
    exact (hLG κ hκ).mono (hh L ((le_max_right _ _).trans hL))
  obtain ⟨q,hq⟩ := hb V D L ((le_max_left _ _).trans hL) M k hk r hconn hbridge w Adm hg scales
  refine ⟨q,?_⟩
  have he : -3*(2*η/3)/4 = -η/2 := by ring
  simpa only [he] using hq

theorem uniform_r23_open_half_gap_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23.pattern),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (AppbPatternKind.r23.pattern).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-η/2))) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hηγ,hη]
  obtain ⟨Lb,hb⟩ := uniform_r23_open_fine_strong_bound
    d hd δ γ (2*η/3) C1 hδ hγ hη' hηγ' hC1
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  have hg : ∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) := by
    intro κ hκ
    exact (hLG κ hκ).mono (hh L ((le_max_right _ _).trans hL))
  obtain ⟨q,hq⟩ := hb V D L ((le_max_left _ _).trans hL) M r hconn hbridge w Adm hg scales
  refine ⟨q,?_⟩
  have he : -3*(2*η/3)/4 = -η/2 := by ring
  simpa only [he] using hq

theorem uniform_r23_triangle_half_gap_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23triangle.pattern),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (AppbPatternKind.r23triangle.pattern).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-η/2))) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hηγ,hη]
  obtain ⟨Lb,hb⟩ := uniform_r23_triangle_fine_strong_bound
    d hd δ γ (2*η/3) C1 hδ hγ hη' hηγ' hC1
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  have hg : ∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) := by
    intro κ hκ
    exact (hLG κ hκ).mono (hh L ((le_max_right _ _).trans hL))
  obtain ⟨q,hq⟩ := hb V D L ((le_max_left _ _).trans hL) M r hconn hbridge w Adm hg scales
  refine ⟨q,?_⟩
  have he : -3*(2*η/3)/4 = -η/2 := by ring
  simpa only [he] using hq

theorem uniform_r23_common_half_gap_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M appbR23Common),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (appbR23Common).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-η/2))) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hηγ,hη]
  obtain ⟨Lb,hb⟩ := uniform_r23_common_fine_strong_bound
    d hd δ γ (2*η/3) C1 hδ hγ hη' hηγ' hC1
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max Lb Lh,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  have hg : ∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) := by
    intro κ hκ
    exact (hLG κ hκ).mono (hh L ((le_max_right _ _).trans hL))
  obtain ⟨q,hq⟩ := hb V D L ((le_max_left _ _).trans hL) M r hconn hbridge w Adm hg scales
  refine ⟨q,?_⟩
  have he : -3*(2*η/3)/4 = -η/2 := by ring
  simpa only [he] using hq

end WaveTurbulence.Mole.AppbAlgorithm
