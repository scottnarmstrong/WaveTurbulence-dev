/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33CutReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBSimpleLocalBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleProjection
public import WaveTurbulence.Foundations.FinalCount.AppBNormalNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
import Mathlib.Tactic

/-! # DH23 split 3S3: normal deviation from exact cut reconstruction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 3s3prop: actual split-geometry count with a concrete post problem. -/
theorem uniform_s33_split_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, 0 < L → ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern),
      M.IsMolecule → AppbS33SplitGeometry M r → ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_tripleFrame_projection_bound d hd γ hγ
  refine ⟨C,L₀,hC,?_⟩
  intro V D instV instF instD L hL hLp δ hδ M r hM hgeom w Adm
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L hL hLp δ hδ M _ r hM (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33.pattern.removed by decide)) (appbS33Frame r) p w Adm
  rw [card_image_of_injOn (appb_s33_split_projection_injective r hgeom p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

/-- The split 3S3 geometry has a normal bound for sufficiently large fixed
C1. This applies in particular to the source 3S3-1N eligibility conditions. -/
theorem uniform_s33_split_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ C₀, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      AppbS33SplitGeometry M r →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      ∃ q : Fin AppbPatternKind.s33.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales) 1 := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_s33_split_countE_bound d hd γ hγ
  refine ⟨max C 1,max L₀ 1,le_max_right C 1,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M r hM hconn hgeom w Adm scales
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) hLp δ hδ M r hM hgeom w Adm
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+2 := by
    have hf := appb_numComponents_eq_two r.post hgeom.1
    have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
    have hh : r.post.circuitRank-M.circuitRank = -2 := by
      rw [r.post_circuitRank,hf,hm]
      norm_num [AppbPatternKind.pattern]
    omega
  have hprod := r.linkProduct_eq_of_simple_table (by decide) L γ δ scales
  have ha := appb_normal_normalization_of_raw _ _ r.post.circuitRank L ((d : ℝ)-γ) δ C1 C
    (appbLinkProduct r.post L γ δ scales) hLp hδ.1
    ((le_max_right C 1).trans hC1) ((le_max_left C 1).trans hC1) hC.le hraw
  unfold IsDeviation appbLinkCountA
  rw [one_mul,hchi,← hprod]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
