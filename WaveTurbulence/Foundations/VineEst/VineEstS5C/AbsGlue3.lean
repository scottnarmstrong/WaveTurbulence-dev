/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsGlue2
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RegionUnique

/-! # `UAbs` of the glued summand, and index/restriction congruences for `UAbs`, `SAbs` (V5 Step 4d part C, `hAbs`) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- Region index congruence for `UAbs`. -/
theorem uAbs_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a') (hb : b = b')
    (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ) :
    UAbs R L base Ψ C ↔ UAbs R' L base Ψ C := by
  subst hU ha hb
  rw [regionData_subsingleton R R']

/-- `UAbs` only sees the summand on the extensions of decorations of the region. -/
theorem uAbs_congr {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (Ψ Ψ' : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ)
    (h : ∀ (z : ↥(clLocalSupport R) → (Fin d → ℤ)) t u, Ψ (clExtendIndices R z) t u = Ψ' (clExtendIndices R z) t u) :
    UAbs R L base Ψ C ↔ UAbs R L base Ψ' C := by
  unfold UAbs
  simp_rw [h]

theorem sAbs_congr {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b) (L : ℝ) (base : Mom d)
    (Ψ Ψ' : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (C : ℝ)
    (h : ∀ (x : GNode G.tree → (Fin d → ℤ)) (e f : Mom d), (∃ y : ExtS RS L base e f, y.1 = x) → ∀ u, Ψ x u = Ψ' x u) :
    SAbs RS L base Ψ C ↔ SAbs RS L base Ψ' C := by
  unfold SAbs
  refine forall_congr' fun t => forall_congr' fun e => forall_congr' fun f => ?_
  have : ∀ x : ExtS RS L base e f, ∀ σ : CLInternalTime RS, Ψ x.1 (clLocalClock RS t σ) = Ψ' x.1 (clLocalClock RS t σ) :=
    fun x σ => h x.1 e f ⟨x, rfl⟩ _
  simp_rw [this]

section Glue
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (L : ℝ) (base : Mom d)
  (ΨU : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
  (ΨS : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (ΨT : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)

include hS hT hi hU in
/-- **`UAbs` of the glued summand** (all exterior data). -/
theorem uAbs_glue (hL : L ≠ 0)
    (hfac : ∀ t0 t1 t2 e f g h, GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t' u = ΨT x t' u')
    (hmS : ∀ x, Measurable (ΨS x))
    (hmT : ∀ x, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => ΨT x z.1 z.2)
    {CS CT : ℝ} (hCT : 0 ≤ CT) (hSa : SAbs RS L base ΨS CS) (hTa : UAbs RT L base ΨT CT) :
    UAbs RU L base ΨU (CS * CT) := by
  intro t β
  obtain ⟨t0, t1, t2, rfl⟩ : ∃ t0 t1 t2 : ℝ, t = ![t0, t1, t2] :=
    ⟨t 0, t 1, t 2, by ext i; fin_cases i <;> rfl⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ e f g h : Mom d, β = ![e, f, g, h] :=
    ⟨β 0, β 1, β 2, β 3, by ext i; fin_cases i <;> rfl⟩
  obtain ⟨⟨hint, hsum⟩, htot⟩ := glueAbs_of_bounds hS hT hi hU RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT (hfac _ _ _ _ _ _ _)
    hlocS hlocT hmS hmT hCT hSa hTa
  set Φ := splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h] with hΦ
  have hfp : ∀ (κ : CLLocalDecoration RU L base ![e, f, g, h]) (τ : CLInternalTime RU),
      fGlue RU RS RT L base t0 t1 t2 e f g h ΨU (Φ κ) τ =
        ΨU (clExtendIndices RU κ.1) ![t0, t1, t2] (clLocalClock RU ![t0, t1, t2] τ) := by
    intro κ τ
    have hx := splitLocalEquiv_symm_val hS hT hi hU RU RS RT hL base ![e, f, g, h] (Φ κ)
    rw [hΦ, Equiv.symm_apply_apply] at hx
    unfold fGlue
    rw [← hx]
  have hfun : ∀ κ, (fun τ => ΨU (clExtendIndices RU κ.1) ![t0, t1, t2] (clLocalClock RU ![t0, t1, t2] τ)) =
      fGlue RU RS RT L base t0 t1 t2 e f g h ΨU (Φ κ) := fun κ => funext fun τ => (hfp κ τ).symm
  refine ⟨fun κ => ?_, ?_, ?_⟩
  · rw [hfun κ]; exact hint (Φ κ)
  · have := (Φ.summable_iff (f := fun p => ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖)).mpr hsum
    refine this.congr fun κ => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => congrArg norm (hfp κ τ))
  · have h1 : ∑' κ : CLLocalDecoration RU L base ![e, f, g, h],
        ∫ τ, ‖ΨU (clExtendIndices RU κ.1) ![t0, t1, t2] (clLocalClock RU ![t0, t1, t2] τ)‖ =
        ∑' p, ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ := by
      refine Eq.trans ?_ (Φ.tsum_eq (fun p => ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖))
      refine tsum_congr fun κ => ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun τ => congrArg norm (hfp κ τ).symm)
    rw [h1]; exact htot

end Glue

end WaveTurbulence.VineEstS5C
