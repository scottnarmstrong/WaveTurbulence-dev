/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33InverseCount
public import WaveTurbulence.Foundations.FinalCount.AppBD33LinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBWeightedNormalNormalization
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalSmallBoundaryEffects
import Mathlib.Tactic

/-! # DH23 3D3-1N with untouched components retained -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- DH23 3d3prop, the log-free normal bound. The scale premises are the
source dyadic range and physical lower gap comparison for the possibly
lost link. A nonexistent lost link has scale zero by definition. -/
theorem uniform_d33_global_normal_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀, ∀ L ≥ L₀, ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      M.IsMolecule →
      (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (appbD33LostScale r scales = 0 ∨ appbD33LostScale r scales ∈ Icc L⁻¹ 1) →
      (∀ κ,Adm κ → 0 < appbD33LostScale r scales → c⁻¹*appbD33LostScale r scales ≤
        ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
          Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖) →
      ∃ q : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales) 1 := by
  obtain ⟨C,hC,hbase⟩ := uniform_d33_inverse_countE_bound d hd γ hγ c hc
  refine ⟨max C 1,le_max_right C 1,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ (Real.exp 1),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hbridge hOpp w Adm scales hscale hgap
  have hexp := (le_max_right L₀ (Real.exp 1)).trans hL
  have hLp := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left L₀ (Real.exp 1)).trans hL) hLp M r hM hOpp w Adm
    (appbD33LostScale r scales) hscale hgap
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+2 := by
    have hh := (global_small_boundary_graph_effects M .d33 (by decide) r hbridge (by decide) (by decide)).2.1
    norm_num only [show AppbPatternKind.d33.pattern.edges.length = 4 by decide,
      show AppbPatternKind.d33.pattern.removed.card = 2 by decide] at hh
    omega
  let X := Molecule.ladderWeight L γ δ (appbD33LostScale r scales)
  have hs0 : 0 ≤ appbD33LostScale r scales := by
    rcases hscale with hzero | hs
    · exact hzero ▸ le_rfl
    · exact (inv_pos.mpr hLp).le.trans hs.1
  have hX : 0 < X := zero_lt_one.trans_le (appb_link_weight_bounds hLp.le hlog hδ.1.le hs0 γ).1
  have hprod : appbLinkProduct M L γ δ scales = X*appbLinkProduct r.post L γ δ scales :=
    appb_d33_linkProduct_factor M hM r L γ δ scales hlog
  have hraw' : (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ))*X⁻¹)*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
    simpa only [X,Molecule.ladderWeight] using hraw
  have ha := appb_normal_normalization_of_raw_inverse_weight _ _ r.post.circuitRank L ((d : ℝ)-γ)
    δ C1 C X (appbLinkProduct r.post L γ δ scales) hLp hδ.1
    ((le_max_right C 1).trans hC1) ((le_max_left C 1).trans hC1) hC.le hX hraw'
  unfold IsDeviation appbLinkCountA
  rw [one_mul,hchi,hprod]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
