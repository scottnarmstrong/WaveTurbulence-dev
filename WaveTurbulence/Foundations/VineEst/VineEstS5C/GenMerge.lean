/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubini

/-! # Merging the S-side with a lower factor of local-summand form, for abstract summands (V5 Step 4d part C, WP-I)

`lkRaw R L base Ψ t β = ∑'_κ ∫_τ Ψ (decoration of κ) t (clock τ)` is the local sum-integral of an abstract summand `Ψ`, a function of the decoration, the exterior times and the CLOCK `u : GBranch → ℝ` (so that it does not depend on the type `CLInternalTime R`).  `lkRaw_split_fubini` is
`clLocalKernel_split_fubini` (VineEstS4/SplitFubini.lean) with `spart` replaced by an abstract S-side integrand `ΨS` and
`clLocalSummand` of `T` by an abstract `ΨT`: if the glued summand factors (`GlueFactors`), `ΨS` reads the clock only on `S`, and
the glued summands converge absolutely (`GlueAbsConv`), then `lkRaw RU ΨU = ∑'_{xS} ∫_σ ΨS(xS, σ) * lkRaw RT ΨT (σ_b, ...)`.
Iterating it merges the nested S-side expressions of the induction over the core vines into ONE local sum-integral of the whole
region (the lower factor `K̃` is itself a `lkRaw`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- The local sum-integral of an abstract summand `Ψ` (decoration, exterior clocks, clock) over a CL region, without constants. -/
noncomputable def lkRaw {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) : ℂ :=
  ∑' κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R, Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)

section Merge
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (L : ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d)
  (ΨU : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
  (ΨS : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (ΨT : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)

/-- The glued summand. -/
noncomputable def fGlue
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (τ : CLInternalTime RU) : ℂ :=
  ΨU (glue RS p.1.1 (clExtendIndices RT p.2.1)) ![t0, t1, t2] (clLocalClock RU ![t0, t1, t2] τ)

include hS hT hi hU in
theorem lkRaw_split_sigma (hL : L ≠ 0) :
    lkRaw RU L base ΨU ![t0, t1, t2] ![e, f, g, h] =
      ∑' p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        ∫ τ, fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ := by
  unfold lkRaw
  rw [← (splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm.tsum_eq]
  refine tsum_congr (fun p => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  have hx := splitLocalEquiv_symm_val hS hT hi hU RU RS RT hL base ![e, f, g, h] p
  simp only [fGlue]
  rw [hx]

/-- The factorisation of the glued summand (hypothesis of the merge). -/
def GlueFactors : Prop :=
  ∀ (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (τ : CLInternalTime RU),
    fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ =
      ΨS p.1.1 (clLocalClock RU ![t0, t1, t2] τ) *
        ΨT (clExtendIndices RT p.2.1) (tT b RU ![t0, t1, t2] τ) (clLocalClock RU ![t0, t1, t2] τ)

include hS hT hi hU in
/-- The glued summand in product coordinates of the times of `S` and `T`. -/
theorem glue_prodForm (hfac : GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t' u = ΨT x t' u') :
    ∃ E : (CLInternalTime RS × CLInternalTime RT) ≃ᵐ CLInternalTime RU, MeasurePreserving E volume volume ∧
      ∀ p σ ρ, fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p (E (σ, ρ)) =
        ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ) := by
  obtain ⟨E0, hE, hl, hr⟩ := exists_timeSplit (clInteriorBranches RU) (S.erase a) (T.erase b)
    (split_interior hS hT hi hU) (split_interior_disjoint hS hT hi hU)
  let E : (CLInternalTime RS × CLInternalTime RT) ≃ᵐ CLInternalTime RU := E0
  refine ⟨E, hE, fun p σ ρ => ?_⟩
  have hclock : ∀ v ∈ S, clLocalClock RU ![t0, t1, t2] (E (σ, ρ)) v = clLocalClock RS ![t0, t1, t2] σ v := by
    intro v hv
    by_cases hva : v = a
    · subst hva
      rw [clLocalClock_upper, clLocalClock_upper]
    · have hv' : v ∈ S.erase a := Finset.mem_erase.mpr ⟨hva, hv⟩
      have h1 := clLocalClock_internal RU ![t0, t1, t2] (E (σ, ρ)) ⟨v, mem_interior_of_S hS hT hi hU hv'⟩
      have h2 := clLocalClock_internal RS ![t0, t1, t2] σ ⟨v, hv'⟩
      rw [h1, h2]
      exact hl σ ρ v hv'
  have hrestr : restrT hS hT hi hU RU RT (E (σ, ρ)) = ρ := by
    funext v
    exact hr σ ρ v.1 v.2
  have htT : tT b RU ![t0, t1, t2] (E (σ, ρ)) = ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] := by
    unfold tT
    rw [hclock b hS.2.2.1]
    rfl
  have hclT : ∀ v ∈ T, clLocalClock RU ![t0, t1, t2] (E (σ, ρ)) v =
      clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ v := by
    intro v hv
    have := clockT hS hT hi hU RU RT ![t0, t1, t2] (E (σ, ρ)) hv
    rw [hrestr, htT] at this
    exact this.symm
  rw [hfac p (E (σ, ρ)), htT]
  exact congrArg₂ (· * ·) (hlocS _ _ _ hclock) (hlocT _ _ _ _ hclT)

/-- Absolute convergence of the glued summands. -/
def GlueAbsConv : Prop :=
  (∀ p, Integrable (fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p)) ∧
    Summable (fun p => ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖)

include hS hT hi hU in
/-- Fubini for one glued summand. -/
theorem glue_fubini_one (hfac : GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t' u = ΨT x t' u')
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (hp : Integrable (fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p)) :
    Integrable (fun σ : CLInternalTime RS => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
        ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
          (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ)) ∧
      ∫ τ, fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ =
        ∫ σ : CLInternalTime RS, ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ) ∧
      ∫ σ : CLInternalTime RS, ‖ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ)‖ ≤
        ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ := by
  obtain ⟨E, hE, hf⟩ := glue_prodForm hS hT hi hU RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT hfac hlocS hlocT
  set f' := fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p with hf'
  have hg : Integrable (f' ∘ E) := (hE.integrable_comp_emb E.measurableEmbedding).mpr hp
  have hrow : ∀ σ, ∫ ρ, (f' ∘ E) (σ, ρ) = ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
      ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
        (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ) := by
    intro σ
    simp only [Function.comp, hf' , hf p σ]
    rw [integral_const_mul]
  have h1 : Integrable (fun σ : CLInternalTime RS => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
        ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
          (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ)) := by
    have := hg.integral_prod_left
    simpa only [hrow] using this
  refine ⟨h1, ?_, ?_⟩
  · rw [← hE.integral_comp' f']
    change ∫ z, (f' ∘ E) z = _
    exact (integral_prod _ hg).trans (integral_congr_ae (Filter.Eventually.of_forall hrow))
  · have hn : Integrable (fun σ => ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖) := hg.norm.integral_prod_left
    calc ∫ σ : CLInternalTime RS, ‖ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ)‖
        ≤ ∫ σ, ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖ := by
          refine integral_mono h1.norm hn (fun σ => ?_)
          rw [← hrow σ]
          exact norm_integral_le_integral_norm _
      _ = ∫ z, ‖(f' ∘ E) z‖ := (integral_prod _ hg.norm).symm
      _ = ∫ τ, ‖f' τ‖ := hE.integral_comp' (fun τ => ‖f' τ‖)

include hS hT hi hU in
/-- **Merge of the S-side with a lower factor of local-summand form (abstract summands).**  If the glued summand factors as
`ΨU = ΨS * ΨT` (`GlueFactors`), `ΨS` reads the clock only on `S`, `ΨT` only on `T`, and the glued summands converge absolutely,
then `lkRaw RU ΨU = ∑'_{xS} ∫_σ ΨS(xS, σ) * lkRaw RT ΨT (σ_b, ...)`. -/
theorem lkRaw_split_fubini (hL : L ≠ 0)
    (hfac : GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t' u = ΨT x t' u')
    (hA : GlueAbsConv RU RS RT L base t0 t1 t2 e f g h ΨU) :
    lkRaw RU L base ΨU ![t0, t1, t2] ![e, f, g, h] =
      ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
        ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
          lkRaw RT L base ΨT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] (bdT RT L base xS.1 g h) := by
  rw [lkRaw_split_sigma hS hT hi hU RU RS RT L base t0 t1 t2 e f g h ΨU hL]
  obtain ⟨hint, hsum⟩ := hA
  have hone := fun p => glue_fubini_one hS hT hi hU RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT hfac hlocS hlocT p (hint p)
  set PhiS : (Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) →
      CLInternalTime RS → ℂ := fun p σ => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
        ∫ ρ : CLInternalTime RT, ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
          (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ) with hPhi
  have h1 : ∀ p, ∫ τ, fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ = ∫ σ, PhiS p σ := fun p => (hone p).2.1
  have hsP : Summable (fun p => ∫ σ, ‖PhiS p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  have hsI : Summable (fun p => ∫ σ, PhiS p σ) :=
    Summable.of_norm_bounded hsP (fun p => norm_integral_le_integral_norm _)
  simp_rw [h1]
  rw [hsI.tsum_sigma' (fun xS => hsI.sigma_factor xS)]
  refine tsum_congr (fun xS => ?_)
  have hsκ : Summable (fun κ => ∫ σ, ‖PhiS ⟨xS, κ⟩ σ‖) := hsP.sigma_factor xS
  have := hasSum_integral_of_summable_integral_norm (fun κ => (hone ⟨xS, κ⟩).1) hsκ
  rw [this.tsum_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
  simp only [lkRaw]
  exact tsum_mul_left

end Merge

end WaveTurbulence.VineEstS5C
