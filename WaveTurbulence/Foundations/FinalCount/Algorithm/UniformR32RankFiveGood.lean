/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32RankFiveCount
public import WaveTurbulence.Foundations.FinalCount.AppBR3CombinedEffects
public import WaveTurbulence.Foundations.FinalCount.AppBSimpleLocalBonds
public import WaveTurbulence.Foundations.FinalCount.AppBLinkLoss
public import WaveTurbulence.Foundations.FinalCount.AppBGoodNormalization
import Mathlib.Tactic

/-! # Good deviation in the five-circuit case of 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

theorem uniform_r32_rank_five_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern),
      M.IsMolecule → s.post.numComponents = M.numComponents →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) →
      ∃ q1 : Fin AppbPatternKind.r3.pattern.edges.length → (Fin d → ℤ),
      ∃ q2 : Fin AppbPatternKind.s33new3.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA s.post L γ δ C1 w
          (s.conditionedPostAdmissibility (r.conditionedPostAdmissibility Adm q1) q2) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_r32_rank_five_countE_bound d hd γ hγ δ hδ
  have hδp := hδ.1
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual (C*δ⁻¹) (3/4) (min γ (1-γ)) 8
      (by positivity) hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r s hM hF w Adm scales hscale
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨q1,q2,hraw⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp M r s hM w Adm
  refine ⟨q1,q2,?_⟩
  have hchi : M.circuitRank = s.post.circuitRank+(5 : ℕ) := by
    obtain ⟨hv,he⟩ := appb_r32_counts M r s
    have hvz : (s.post.atoms.card : ℤ)+3 = M.atoms.card := by exact_mod_cast hv
    have hez : (s.post.bonds.card : ℤ)+8 = M.bonds.card := by exact_mod_cast he
    unfold Molecule.circuitRank
    rw [hF]
    omega
  have hcard : s.removedAtoms.card = 2 := by
    change (AppbPatternKind.s33new3.pattern.removed.image s.vertex).card = 2
    rw [card_image_of_injOn (fun a ha b hb h => s.vertex_injective
      (mem_union_left _ ha) (mem_union_left _ hb) h)]
    decide
  have hlinks : appbLinkProduct M L γ δ scales ≤ Real.log L^8*appbLinkProduct s.post L γ δ scales := by
    rw [← r.linkProduct_eq_of_simple_table (by decide) L γ δ scales]
    have hh := appbLinkProduct_eraseAtoms_bound r.post (appb_eraseAtoms_isMolecule M hM r.removedAtoms)
      s.removedAtoms L γ δ scales hLp.le hlog hδ.1.le hscale
    rw [hcard,show 4*2 = 8 by decide] at hh
    simpa only [AppbRealization.post] using hh
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have ha := appb_good_normalization_of_raw _ _ s.post.circuitRank 5 8 L ((d : ℝ)-γ)
    (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct M L γ δ scales) (appbLinkProduct s.post L γ δ scales)
    (C*δ⁻¹) (3/4) (min γ (1-γ)) hL1 hB hB1 (by positivity) hlinks
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL))) (by
      have he : ((d : ℝ)-γ)*(5 : ℝ)-(3/4)*min γ (1-γ) =
          5*((d : ℝ)-γ)-3*min γ (1-γ)/4 := by ring
      simpa only [Nat.cast_ofNat,he] using hraw)
  unfold IsDeviation appbLinkCountA
  rw [hchi]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
