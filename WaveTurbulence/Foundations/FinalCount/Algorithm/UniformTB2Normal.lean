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

end WaveTurbulence.Mole.AppbAlgorithm
