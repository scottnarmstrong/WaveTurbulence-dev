/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformCutTripleCount
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
public import WaveTurbulence.Foundations.FinalCount.AppBD33SameCutSigns
public import WaveTurbulence.Foundations.FinalCount.AppBD33Reconstruction
import Mathlib.Tactic

/-! # Actual counting for the same-direction double-pair operation 3D3-4G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d33_same_direction_countE_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      (¬AppbD33BoundaryOpposite M r) → ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_cut_triple_card_bound_of_projection_injective
    d hd γ hγ δ η hδ hη hηγ 1
  refine ⟨max L₀ (Real.exp 1),?_⟩
  intro V D instV instF instD L hL hLp M r hsame w Adm hLG
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr ((le_max_right _ _).trans hL)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hcard : (r.removedAtoms.card : ℝ) ≤ (1+Real.log L)^1 := by
    have hc : r.removedAtoms.card ≤ 2 := by
      change (AppbPatternKind.d33.pattern.removed.image r.vertex).card ≤ 2
      exact card_image_le.trans (by decide)
    have hc' : (r.removedAtoms.card : ℝ) ≤ 2 := by exact_mod_cast hc
    simpa only [pow_one] using hc'.trans (by linarith only [hlog])
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide)
  have hN := hL₀ V D L ((le_max_left _ _).trans hL) hLp M _ r r.removedAtoms (appbD33CutPair r)
    (appb_d33_cut_signs_same M r hsame) hcard (r.vertex 1) hv (appbD33Frame r) rfl p w Adm
    (appb_d33_projection_injective r p hLp γ δ w Adm) (by
      intro hsign κ hκ
      exact appb_tripleFrame_pair_gap r (appbD33Frame r) hv L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
