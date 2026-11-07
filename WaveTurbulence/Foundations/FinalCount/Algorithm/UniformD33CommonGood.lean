/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33CommonCount
public import WaveTurbulence.Foundations.FinalCount.AppBGoodDeletionTransfer
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
import Mathlib.Tactic

/-! # Good deviation for the common-neighbour branch 3D3-5G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset Filter
open scoped ENNReal
universe u v

/-- DH23 3D3-5G, with a common boundary neighbour and the standing LG premise. -/
theorem uniform_d33_common_good_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ C1 ≥ (1 : ℝ), ∀ L ≥ L₀,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33same.pattern),
      M.IsMolecule → (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) →
      (∀ e : D,¬Degen.IsBridge M e) →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
      (∀ S,0 ≤ scales S) →
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin AppbPatternKind.d33same.pattern.edges.length → (Fin d → ℤ),
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm scales)
        (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility Adm q) scales)
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) := by
  intro δ hδ
  obtain ⟨C,hC,L₀,hL₀⟩ := uniform_d33_common_countE_bound d hd γ hγ δ η hδ hη hηγ
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp
    (appb_good_log_coefficient_eventual C (31/48) (min γ (1-γ)) 8 hC.le hg0 (by norm_num))
  refine ⟨max L₀ (max L₁ (Real.exp 1)),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hconn hbridge w Adm scales hscale hgap
  have hexp : Real.exp 1 ≤ L := (le_max_right L₁ _).trans ((le_max_right L₀ _).trans hL)
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hLp := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  obtain ⟨q,hraw⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp M r hM w Adm hgap
  refine ⟨q,?_⟩
  have hchi : M.circuitRank = r.post.circuitRank+(2 : ℕ) := by
    have hh := (r.small_boundary_graph_effects hconn hbridge (by decide) (by decide) (by decide)).2.1
    have he : AppbPatternKind.d33same.pattern.edges.length = 4 := by decide
    have hv : AppbPatternKind.d33same.pattern.removed.card = 2 := by decide
    rw [he,hv] at hh
    omega
  have hcard : 4*r.removedAtoms.card ≤ 8 := by
    change 4*(AppbPatternKind.d33same.pattern.removed.image r.vertex).card ≤ 8
    have hh := card_image_le (f := r.vertex) (s := AppbPatternKind.d33same.pattern.removed)
    have hn : AppbPatternKind.d33same.pattern.removed.card = 2 := by decide
    omega
  apply appb_good_deletion_of_raw_and_rank r hM L γ δ C1 (31/48) (min γ (1-γ)) C
    w Adm q scales 2 8 hL1 hlog hδ hC1 hC.le hscale hcard hchi
    (hL₁ L ((le_max_left L₁ _).trans ((le_max_right L₀ _).trans hL)))
  have he : ((d : ℝ)-γ)*(2 : ℝ)-(31/48)*min γ (1-γ) =
      2*((d : ℝ)-γ)-31*min γ (1-γ)/48 := by ring
  simpa only [Nat.cast_ofNat,he] using hraw

end WaveTurbulence.Mole.AppbAlgorithm
