/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR23Counts
public import WaveTurbulence.Foundations.FinalCount.AppBFineStrongTransfer
public import WaveTurbulence.Foundations.FinalCount.AppBTwoRemovalEffects
import Mathlib.Tactic

/-! # DH23 2R-3F fine deviations in all actual incidence layouts -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 2rprop, 2R-3F open layout, with the source graph and LG
premises. The refined ladder product is preserved exactly. -/
theorem uniform_r23_open_fine_strong_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23.pattern),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (AppbPatternKind.r23.pattern).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-3*η/4))) := by
  obtain ⟨L₀,hL₀⟩ := uniform_r23_open_countE_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) M r w Adm hLG
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+1 := by
    have hh := (appb_r2_open_graph_effect M .r23 (by simp) r hconn hbridge).2.1
    omega
  have hlow : ∀ a ∈ r.removedAtoms,M.deg a ≤ 2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    rw [r.deleted_degree b hb]
    change b ∈ ({1,2,3} : Finset ℕ) at hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> decide
  exact appb_link_fine_strong_of_countE_and_rank r L γ δ C1 η w Adm q scales
    ((le_max_right L₀ 1).trans hL) hδ hC1 hη.le hlow hchi hraw

/-- DH23 2rprop, 2R-3F triangle layout, with the source graph and LG
premises. The refined ladder product is preserved exactly. -/
theorem uniform_r23_triangle_fine_strong_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23triangle.pattern),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (AppbPatternKind.r23triangle.pattern).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-3*η/4))) := by
  obtain ⟨L₀,hL₀⟩ := uniform_r23_triangle_countE_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) M r w Adm hLG
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+1 := by
    have hh := (appb_r2_closed_graph_effect M .r23triangle (by simp) r hconn).2.2.1
    omega
  have hlow : ∀ a ∈ r.removedAtoms,M.deg a ≤ 2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    rw [r.deleted_degree b hb]
    change b ∈ ({1,2,3} : Finset ℕ) at hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> decide
  exact appb_link_fine_strong_of_countE_and_rank r L γ δ C1 η w Adm q scales
    ((le_max_right L₀ 1).trans hL) hδ hC1 hη.le hlow hchi hraw

/-- DH23 2rprop, 2R-3F common layout, with the source graph and LG
premises. The refined ladder product is preserved exactly. -/
theorem uniform_r23_common_fine_strong_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M appbR23Common),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin (appbR23Common).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-3*η/4))) := by
  obtain ⟨L₀,hL₀⟩ := uniform_r23_common_countE_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r hconn hbridge w Adm hLG scales
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) M r w Adm hLG
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+1 := by
    have hh := (appb_r23_common_graph_effect M r hconn hbridge).2.1
    omega
  have hlow : ∀ a ∈ r.removedAtoms,M.deg a ≤ 2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    rw [r.deleted_degree b hb]
    change b ∈ ({1,2,3} : Finset ℕ) at hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> decide
  exact appb_link_fine_strong_of_countE_and_rank r L γ δ C1 η w Adm q scales
    ((le_max_right L₀ 1).trans hL) hδ hC1 hη.le hlow hchi hraw

end WaveTurbulence.Mole.AppbAlgorithm
