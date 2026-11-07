/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeCounting
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeLinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeGraphEffects
import Mathlib.Tactic

/-! # DH23 BR-N: the actual normal deviation inequality -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 brprop: bridge removal has deviation at most (log L)^8 in the
refined invariant. The concrete inherited post predicate and post scales
are explicit, and zero post counts are included. -/
theorem appb_bridge_normal_bound (M : Molecule V D) (hM : M.IsMolecule) (e : D)
    (hb : Degen.IsBridge M e) {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ C1 : ℝ)
    (hlog : 1 ≤ Real.log L) (hδ : 0 < δ) (hC1 : 0 < C1) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hP : ∀ S,0 ≤ P S) :
    ∃ q : Fin d → ℤ,
      IsDeviation (appbLinkCountA M L γ δ C1 w Adm P)
        (appbLinkCountA (eraseBond M e) L γ δ C1 w (appbBridgePostAdmissibility M e Adm q)
          (appbBridgeScales M e P)) (ENNReal.ofReal (Real.log L^8)) := by
  obtain ⟨q,hE⟩ := appb_bridge_countE_exists_post M e hb hL γ δ w Adm
  refine ⟨q,?_⟩
  have hE' := ENat.toENNReal_mono hE
  have hχ := appb_bridge_circuitRank M e hb
  have hprod := appb_bridge_linkProduct_bound M hM e L γ δ P hL.le hlog hδ.le hP
  have hfac : 0 ≤ L^(-((d : ℝ)-γ)*(M.circuitRank : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank := by
    positivity
  have hnorm :
      L^(-((d : ℝ)-γ)*(M.circuitRank : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank*
        appbLinkProduct M L γ δ P ≤
      Real.log L^8*(L^(-((d : ℝ)-γ)*(M.circuitRank : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank*
        appbLinkProduct (eraseBond M e) L γ δ (appbBridgeScales M e P)) :=
    (mul_le_mul_of_nonneg_left hprod hfac).trans_eq (by ring)
  have hw := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul (pow_nonneg (by linarith only [hlog] : 0 ≤ Real.log L) 8)] at hw
  unfold IsDeviation appbLinkCountA
  rw [hχ]
  calc
    _ ≤ (appbCountE (eraseBond M e) L γ δ w (appbBridgePostAdmissibility M e Adm q) : ℝ≥0∞)*
        ENNReal.ofReal (L^(-((d : ℝ)-γ)*(M.circuitRank : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^M.circuitRank*
          appbLinkProduct M L γ δ P) := mul_le_mul_left hE' _
    _ ≤ _ := by
      have hh := mul_le_mul_right hw
        (appbCountE (eraseBond M e) L γ δ w (appbBridgePostAdmissibility M e Adm q) : ℝ≥0∞)
      exact hh.trans_eq (by ring)

end WaveTurbulence.Mole
