/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32RankFourCount
public import WaveTurbulence.Foundations.FinalCount.AppBCombinedEffects
public import WaveTurbulence.Foundations.FinalCount.AppBGoodDeletionTransfer
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # The full good deviation in the four-circuit branch of 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

theorem uniform_r32_rank_four_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) → (∀ e : D,¬Degen.IsBridge M e) → s.post.numComponents = 2 →
      (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) → (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA (r.combinedRemoval s v0).post L γ δ C1 w ((r.combinedRemoval s v0).conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_r32_rank_four_countE_bound d hd γ hγ δ η hδ hη hηγ m
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual C (31/48) (min γ (1-γ)) 12 hC.le hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r s v0 hM hc hb hF hsize w Adm scales hscale hLG
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp M r s v0 hM hsize hc hb hF w Adm hLG
  refine ⟨q,?_⟩
  let b := r.combinedRemoval s v0
  have hchi : M.circuitRank = b.post.circuitRank+(4 : ℕ) := by
    have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hc
    have hh := b.post_circuitRank
    have hbc := r.combinedRemoval_components s v0
    have hrc := r.combinedPattern_removed_card s v0
    have hlen := r.combinedPattern_length s
    change b.post.numComponents = s.post.numComponents at hbc
    rw [hbc,hF,hm] at hh
    norm_num [AppbPatternKind.pattern] at hrc hlen
    omega
  have hcard : 4*b.removedAtoms.card ≤ 12 := by
    have hh := r.combinedRemoval_removed_card s v0
    norm_num [AppbPatternKind.pattern] at hh
    change 4*(r.combinedRemoval s v0).removedAtoms.card ≤ 12
    omega
  apply appb_good_deletion_of_raw_and_rank b hM L γ δ C1 (31/48) (min γ (1-γ)) C
    w Adm q scales 4 12 hL1 hlog hδ hC1 hC.le hscale hcard hchi
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL)))
  have he : ((d : ℝ)-γ)*(4 : ℝ)-(31/48)*min γ (1-γ) =
      4*((d : ℝ)-γ)-31*min γ (1-γ)/48 := by ring
  simpa only [Nat.cast_ofNat,he] using hraw

end WaveTurbulence.Mole.AppbAlgorithm
