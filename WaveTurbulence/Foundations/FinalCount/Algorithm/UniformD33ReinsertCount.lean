/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertParameters
public import WaveTurbulence.Foundations.FinalCount.AppBD33Reconstruction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformReinsertFiberCount
public import WaveTurbulence.Foundations.FinalCount.AppBOneWindowCount
import Mathlib.Tactic

/-! # Actual decoration count for the good double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 3D3-3G raw count with the concrete inherited post predicate.
The factor eight comes from one three-window energy interval; the internal
pair is counted uniformly for each actual copied boundary label. -/
theorem uniform_d33_reinsert_countE_bound (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      AppbD33BoundaryOpposite M r → ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (8*L^((d : ℝ)-γ-31*min γ (1-γ)/48))*
          (appbCountE (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ w
            (r.reinsertedPostAdmissibility Adm ⟨2,by decide⟩) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_reinsert_card_le_of_frame_injective d hd δ γ hδ hγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hOpp w Adm htest
  obtain ⟨p,hp⟩ := appbCountE_attained M hLp γ δ w Adm
  let S := (p.decorations_finite hLp γ δ w Adm).toFinset
  have hS : ∀ κ ∈ S,κ ∈ p.decorations L γ δ w Adm := by
    intro κ hκ
    exact ((p.decorations_finite hLp γ δ w Adm).mem_toFinset).mp hκ
  have hcardS : (S.card : ℕ∞) = appbCountE M L γ δ w Adm :=
    (p.decorations_finite hLp γ δ w Adm).encard_eq_coe_toFinset_card.symm.trans hp
  have hpair := hL₀ V D L hL hLp M _ r (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide)) (appbD33Frame r) p w Adm
    (appb_d33_projection_injective r p hLp γ δ w Adm) (by
      intro hsign κ hκ
      exact (htest κ hκ.2.2).2 ((appb_incidence_sign_opposite M (r.vertex 1) _ _).mp hsign)) S hS
  let N := r.directedPostWithBond 3 4 ⟨2,by decide⟩
  let Adm' := r.reinsertedPostAdmissibility Adm ⟨2,by decide⟩
  let T := S.image (fun κ => r.reinsertedLabels κ ⟨2,by decide⟩)
  have hv4 : r.vertex 4 ∈ N.atoms := by
    unfold N AppbRealization.directedPostWithBond
    split_ifs
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · exact mem_insert_self _ _
  have hpost : (T.card : ℕ∞) ≤ 8*appbCountE N L γ δ w Adm' := by
    have hh := appb_one_window_count_le N hLp hδ.1 w (appbD33ReinsertParameters r p) Adm'
      (r.vertex 4) hv4 3 T (by
        intro ζ hζ
        obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hζ
        have hk := hS κ hκ
        exact ⟨appb_d33_reinsert_isDecoration r hOpp L w p.momentum κ hk.1,
          r.reinsertedPostAdmissibility_map Adm _ κ hk.2.2 hk.1.1,
          appb_d33_reinsert_spatial r L γ δ w p κ hk.2.1,
          appb_d33_reinsert_energy_window r hOpp L γ δ w p κ hk.1 hk.2.1⟩)
    norm_num at hh
    exact hh
  have hpair' : (S.card : ℝ) ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48)*(T.card : ℝ) := hpair
  have hraw : (S.card : ℝ≥0∞) ≤ ENNReal.ofReal (L^((d : ℝ)-γ-31*min γ (1-γ)/48))*(T.card : ℝ≥0∞) := by
    have hh := ENNReal.ofReal_le_ofReal hpair'
    simpa only [ENNReal.ofReal_natCast,ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)] using hh
  have hpost' : (T.card : ℝ≥0∞) ≤ 8*(appbCountE N L γ δ w Adm' : ℝ≥0∞) := by
    have hh := ENat.toENNReal_mono hpost
    simpa only [ENat.toENNReal_mul,ENat.toENNReal_coe,ENat.toENNReal_ofNat] using hh
  have hS' : (S.card : ℝ≥0∞) = (appbCountE M L γ δ w Adm : ℝ≥0∞) :=
    congrArg ENat.toENNReal hcardS
  rw [← hS']
  refine (hraw.trans (mul_le_mul_right hpost' _)).trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),ENNReal.ofReal_ofNat]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
