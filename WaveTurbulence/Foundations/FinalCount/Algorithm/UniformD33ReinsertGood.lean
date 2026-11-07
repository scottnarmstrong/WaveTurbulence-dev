/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33ReinsertCount
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertLinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBGoodNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # The full good deviation for actual double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

/-- DH23 3D3-3G. All post counts use the actual copied boundary label,
fixed post source parameters, one finite energy bin, and the inherited
admissibility predicate. The post link scales retain the old scales away
from the deleted atoms and the reinserted endpoints. -/
theorem uniform_d33_reinsert_good_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) →
      (∀ κ,Adm κ → AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1 w
          (r.reinsertedPostAdmissibility Adm ⟨2,by decide⟩)
          (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 4) scales))
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := uniform_d33_reinsert_countE_bound d hd δ γ hδ hγ
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual 8 (31/48) (min γ (1-γ)) 16 (by norm_num) hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hconn hbridge hOpp w Adm scales hscale htest
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  let N := r.directedPostWithBond 3 4 ⟨2,by decide⟩
  let Ps := appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 4) scales
  have hraw := hL₀ V D L ((le_max_left _ _).trans hL) hLp M r hOpp w Adm htest
  have hcard : r.removedAtoms.card = 2 := by
    change (AppbPatternKind.d33.pattern.removed.image r.vertex).card = 2
    rw [card_image_of_injOn (fun a ha b hb h => r.vertex_injective
      (mem_union_left _ ha) (mem_union_left _ hb) h)]
    decide
  have hlinks : appbLinkProduct M L γ δ scales ≤ Real.log L^16*appbLinkProduct N L γ δ Ps := by
    by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3
    · have hh := appb_reinsert_linkProduct_bound M hM r.removedAtoms (r.vertex 3) (r.vertex 4)
        L γ δ scales hLp.le hlog hδ.1.le hscale
      rw [hcard,show 4*(2+2) = 16 by decide] at hh
      dsimp only [N]
      rw [AppbRealization.directedPostWithBond,if_pos ha]
      exact hh
    · have hh := appb_reinsert_linkProduct_bound M hM r.removedAtoms (r.vertex 4) (r.vertex 3)
        L γ δ scales hLp.le hlog hδ.1.le hscale
      rw [hcard,show 4*(2+2) = 16 by decide] at hh
      have hP : appbReinsertScales M r.removedAtoms (r.vertex 4) (r.vertex 3) scales = Ps := by
        funext S
        change appbReinsertScales M r.removedAtoms (r.vertex 4) (r.vertex 3) scales S =
          appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 4) scales S
        unfold appbReinsertScales
        rw [Finset.pair_comm]
      rw [hP] at hh
      dsimp only [N]
      rw [AppbRealization.directedPostWithBond,if_neg ha]
      exact hh
  have hchi : M.circuitRank = N.circuitRank+(1 : ℕ) := by
    have hh := (appb_d33_good_reinsert_graph_effect M r hconn hbridge).2.1
    change N.circuitRank-M.circuitRank = -1 at hh
    omega
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ.1 _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 :=
    (mul_le_mul ((inv_le_one₀ hCpos).mpr hC1)
      (Real.rpow_le_one hδ.1.le hδ.2 (by norm_num))
      (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hraw' : (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
      ENNReal.ofReal (8*L^(((d : ℝ)-γ)*(1 : ℝ)-(31/48)*min γ (1-γ)))*
        (appbCountE N L γ δ w (r.reinsertedPostAdmissibility Adm ⟨2,by decide⟩) : ℝ≥0∞) := by
    have he : ((d : ℝ)-γ)*(1 : ℝ)-(31/48)*min γ (1-γ) =
        (d : ℝ)-γ-31*min γ (1-γ)/48 := by ring
    simpa only [he] using hraw
  have ha := appb_good_normalization_of_raw _ _ N.circuitRank 1 16 L ((d : ℝ)-γ)
    (C1⁻¹*δ^(1/2 : ℝ)) (appbLinkProduct M L γ δ scales) (appbLinkProduct N L γ δ Ps)
    8 (31/48) (min γ (1-γ)) hL1 hB hB1 (by norm_num) hlinks
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL))) (by simpa only [Nat.cast_one] using hraw')
  unfold IsDeviation appbLinkCountA
  rw [hchi]
  exact ha

end WaveTurbulence.Mole.AppbAlgorithm
