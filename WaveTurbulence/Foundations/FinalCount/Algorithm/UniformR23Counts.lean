/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR23Reconstruction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformPairProjection
import Mathlib.Tactic

/-! # Actual raw counting bounds in all 2R-3F layouts -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 2R-3F, open layout: a concrete conditioned post problem with
the raw fine saving, derived from the actual central-pair reconstruction. -/
theorem uniform_r23_open_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23.pattern)
      (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (AppbPatternKind.r23.pattern).edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_localPair_projection_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r w Adm hLG
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L ((le_max_left L₀ 1).trans hL) M _ r (r.vertex 1)
    (appbR23_open_central r) (mem_image_of_mem _ (show 1 ∈ (AppbPatternKind.r23.pattern).removed by decide)) p w Adm hLG hLp
  rw [card_image_of_injOn (appb_r23_open_projection_injective r p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

/-- DH23 2R-3F, triangle layout: a concrete conditioned post problem with
the raw fine saving, derived from the actual central-pair reconstruction. -/
theorem uniform_r23_triangle_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r23triangle.pattern)
      (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (AppbPatternKind.r23triangle.pattern).edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_localPair_projection_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r w Adm hLG
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L ((le_max_left L₀ 1).trans hL) M _ r (r.vertex 1)
    (appbR23_triangle_central r) (mem_image_of_mem _ (show 1 ∈ (AppbPatternKind.r23triangle.pattern).removed by decide)) p w Adm hLG hLp
  rw [card_image_of_injOn (appb_r23_triangle_projection_injective r p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

/-- DH23 2R-3F, common layout: a concrete conditioned post problem with
the raw fine saving, derived from the actual central-pair reconstruction. -/
theorem uniform_r23_common_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M appbR23Common)
      (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (appbR23Common).edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤ ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_localPair_projection_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD L hL M r w Adm hLG
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L ((le_max_left L₀ 1).trans hL) M _ r (r.vertex 1)
    (appbR23_common_central r) (mem_image_of_mem _ (show 1 ∈ (appbR23Common).removed by decide)) p w Adm hLG hLp
  rw [card_image_of_injOn (appb_r23_common_projection_injective r p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^((d : ℝ)-γ-3*η/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
