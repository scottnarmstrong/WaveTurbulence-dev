/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleCut
public import WaveTurbulence.Foundations.FinalCount.AppBD33Reconstruction
import Mathlib.Tactic

/-! # The inverse-weight double-pair estimate with carrier-uniform constants -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v
/-- DH23 basiccount(3), on the actual double-pair labels with the source
boundary direction and physical scale comparison. No count bound is
assumed; the two-atom cut supplies its conserved vector and energy strip. -/
theorem uniform_d33_inverse_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀,
    ∀ hLp : 0 < L, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      M.IsMolecule → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scale : ℝ),
      (scale = 0 ∨ scale ∈ Icc L⁻¹ 1) →
      (∀ κ,Adm κ → 0 < scale → c⁻¹*scale ≤
        ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖) →
      ∃ q : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*scale))⁻¹)*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨C,hC,hbase⟩ := uniform_triple_cut_projection_bound d hd γ hγ c hc
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hM hOpp w Adm scale hscale hgap
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hcard : r.removedAtoms.card ≤ 2 := by
    change (AppbPatternKind.d33.pattern.removed.image r.vertex).card ≤ 2
    exact card_image_le.trans (by decide)
  have hN := hL₀ V D L hL hLp M _ r hM (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide)) (appbD33Frame r)
    r.removedAtoms (appbD33CutPair r) (appb_d33_cut_signs_opposite M r hOpp) hcard 2 rfl p w Adm scale hscale hgap
  rw [card_image_of_injOn (appb_d33_projection_injective r p hLp γ δ w Adm)] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*scale))⁻¹) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
