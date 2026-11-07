/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTB2Reconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBTB2Links
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleProjection
public import WaveTurbulence.Foundations.FinalCount.AppBNormalNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBTripleBondEffects
import Mathlib.Tactic

/-! # DH23 TB-2N: actual normal deviation with reconstructed external label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 tbprop, TB-2N: actual counting with a concrete post problem. -/
theorem uniform_tb2_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, 0 < L → ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.tb2.pattern),
      M.IsMolecule → ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin AppbPatternKind.tb2.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_tripleFrame_projection_bound d hd γ hγ
  refine ⟨C,L₀,hC,?_⟩
  intro V D instV instF instD L hL hLp δ hδ M r hM w Adm
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L hL hLp δ hδ M _ r hM (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.tb2.pattern.removed by decide)) (appbTB2Frame r) p w Adm
  rw [card_image_of_injOn (appb_tb2_projection_injective r p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

/-- TB-2N makes the refined invariant nonincreasing for a fixed sufficiently
large C1, hence obeys the requested normal deviation bound. -/
theorem uniform_tb2_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ C₀, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.tb2.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      ∃ q : Fin AppbPatternKind.tb2.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales) 1 := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_tb2_countE_bound d hd γ hγ
  refine ⟨max C 1,max L₀ 1,le_max_right C 1,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M r hM hconn w Adm scales
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ 1).trans hL) hLp δ hδ M r hM w Adm
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+2 := by
    have hh := (appb_tb2_graph_effect M r hconn).2.1
    omega
  have hprod := appb_tb2_linkProduct M r L γ δ scales
  have ha := appb_normal_normalization_of_raw _ _ r.post.circuitRank L ((d : ℝ)-γ) δ C1 C
    (appbLinkProduct r.post L γ δ scales) hLp hδ.1
    ((le_max_right C 1).trans hC1) ((le_max_left C 1).trans hC1) hC.le hraw
  unfold IsDeviation appbLinkCountA
  rw [one_mul,hchi,← hprod]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
