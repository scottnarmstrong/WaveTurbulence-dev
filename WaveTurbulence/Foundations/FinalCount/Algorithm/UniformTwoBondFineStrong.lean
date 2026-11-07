/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTwoBondCount
public import WaveTurbulence.Foundations.FinalCount.AppBFineStrongNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBTwoRemovalEffects
import Mathlib.Tactic

/-! # Fine deviation for the actual two-bond degree-two operations

These are 2R-1F, 2R-2F and 2R-4F, using the refined local-link invariant.
Its initial agreement with the source product is proved separately.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_r2_two_bond_fine_strong_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (k : AppbPatternKind),
      k ∈ ([AppbPatternKind.r21,.r22,.r24] : List _) →
      ∀ r : AppbRealization M k.pattern,
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ scales : Finset V → ℝ,
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-3*η/4))) := by
  obtain ⟨L₀,hL₀⟩ := uniform_two_bond_countE_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M k hk r hconn hbridge w Adm hLG scales
  have hL1 := (le_max_right L₀ 1).trans hL
  have hlen : k.pattern.edges.length = 2 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · rfl
    rcases List.mem_cons.mp hk with rfl | hk
    · rfl
    have he := List.mem_singleton.mp hk
    subst k
    rfl
  have h1 : 1 ∈ k.pattern.removed := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ h1
  have hinc : ∀ i,appbIncidence M (r.vertex 1) (r.edge i).val = 1 := by
    intro i
    rw [r.edge_incidence i 1 (mem_union_left _ h1)]
    rcases List.mem_cons.mp hk with rfl | hk
    · fin_cases i <;> decide
    rcases List.mem_cons.mp hk with rfl | hk
    · fin_cases i <;> decide
    have he := List.mem_singleton.mp hk
    subst k
    fin_cases i <;> decide
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) M k.pattern r hlen (r.vertex 1) hv hinc w Adm hLG
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+1 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · have hh := (appb_r2_open_graph_effect M .r21 (by simp) r hconn hbridge).2.1
      omega
    rcases List.mem_cons.mp hk with rfl | hk
    · have hh := (appb_r2_open_graph_effect M .r22 (by simp) r hconn hbridge).2.1
      omega
    have he := List.mem_singleton.mp hk
    subst k
    have hh := (appb_r2_closed_graph_effect M .r24 (by simp) r hconn).2.2.1
    omega
  have hlow : ∀ a ∈ r.removedAtoms,M.deg a ≤ 2 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    rw [r.deleted_degree b hb]
    rcases List.mem_cons.mp hk with rfl | hk
    · have he : b = 1 := by simpa [AppbPatternKind.pattern] using hb
      subst b
      decide
    rcases List.mem_cons.mp hk with rfl | hk
    · have he : b = 1 := by simpa [AppbPatternKind.pattern] using hb
      subst b
      decide
    have he := List.mem_singleton.mp hk
    subst k
    have he : b = 1 ∨ b = 2 := by simpa [AppbPatternKind.pattern] using hb
    rcases he with rfl | rfl <;> decide
  have hprod := appbLinkProduct_eraseAtoms_low_degree M r.removedAtoms hlow L γ δ scales
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have ha := appb_fine_normalization_strong_of_raw _ _ r.post.circuitRank L ((d : ℝ)-γ)
    (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct r.post L γ δ scales) η hL1 hB hB1 hη.le hraw
  unfold IsDeviation appbLinkCountA
  rw [hchi,← hprod]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
