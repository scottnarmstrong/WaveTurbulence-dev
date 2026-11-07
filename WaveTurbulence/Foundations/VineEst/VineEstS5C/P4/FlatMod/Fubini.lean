/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.TwistLF
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubiniInputs
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp12Sok
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsMeas

/-! # FLAT-MOD (R60), kernel level 3: the Fubini split of the modulated kernel at a joint

`e^{πiλτ_c}` (`c` the lower joint of `U = S ∪ T`) is the modulation of the lower block `T` at its own lower joint, evaluated at the
restricted times (`clockT`): so the glued modulated summand is `spart · (modulated T-summand)`, and `K^{U,λ}` is the S-side with lower
factor `K^{T,λ}` (`clLocalKernelModC_split_KT`, modulated `clLocalKernel_split_KT`), with `SOK` (`sok_KTM`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

theorem measurable_lowModC {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (lam : ℝ) (t : Fin 3 → ℝ) :
    Measurable (lowModC R lam t) := by
  unfold lowModC
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_const.mul (measurable_clLocalClock R t b))).mul measurable_const)

theorem lowModC_mul_integrable {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b) (lam : ℝ) (t : Fin 3 → ℝ)
    {f : CLInternalTime R → ℂ} (hf : Integrable f) : Integrable fun τ => lowModC R lam t τ * f τ :=
  hf.bdd_mul (c := 1) ((measurable_lowModC R lam t).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun τ => (norm_lowModC R lam t τ).le)

section Fubini
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

/-- The modulated glued summand. -/
noncomputable def fUM
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (τ : CLInternalTime RU) : ℂ :=
  lowModC RU lam ![t0, t1, t2] τ *
    fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ

/-- Absolute convergence of the modulated glued summands. -/
def AbsConvM : Prop :=
  (∀ p, Integrable (fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p)) ∧
    Summable (fun p => ∫ τ, ‖fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ‖)

theorem norm_fUM (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (τ : CLInternalTime RU) :
    ‖fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ‖ =
      ‖fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ‖ := by
  unfold fUM
  rw [norm_mul, norm_lowModC, one_mul]

include hS hT hi hU in
theorem absConvM_of_inputs (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    AbsConvM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h := by
  obtain ⟨h1, h2⟩ := absConv_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL hF
  refine ⟨fun p => lowModC_mul_integrable RU lam _ (h1 p), ?_⟩
  refine h2.congr fun p => ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
    (norm_fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ).symm)

include hS hT hi hU in
/-- The glued modulated summand in product coordinates `(σ, ρ)`. -/
theorem exists_prodFormM :
    ∃ E : (CLInternalTime RS × CLInternalTime RT) ≃ᵐ CLInternalTime RU, MeasurePreserving E volume volume ∧
      ∀ p σ ρ, fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p (E (σ, ρ)) =
        spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
          (lowModC RT lam ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ *
            clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
              ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] p.2 ρ) := by
  obtain ⟨E, hE, hl, hr⟩ := exists_timeSplit (clInteriorBranches RU) (S.erase a) (T.erase b)
    (split_interior hS hT hi hU) (split_interior_disjoint hS hT hi hU)
  have hclock : ∀ (σ0 : CLInternalTime RS) (ρ0 : CLInternalTime RT), ∀ v ∈ S,
      clLocalClock RU ![t0, t1, t2] (E (σ0, ρ0)) v = clLocalClock RS ![t0, t1, t2] σ0 v := by
    intro σ0 ρ0 v hv
    by_cases hva : v = a
    · subst hva
      rw [clLocalClock_upper, clLocalClock_upper]
    · have hv' : v ∈ S.erase a := Finset.mem_erase.mpr ⟨hva, hv⟩
      have h1 := clLocalClock_internal RU ![t0, t1, t2] (E (σ0, ρ0)) ⟨v, mem_interior_of_S hS hT hi hU hv'⟩
      have h2 := clLocalClock_internal RS ![t0, t1, t2] σ0 ⟨v, hv'⟩
      rw [h1, h2]
      exact hl σ0 ρ0 v hv'
  have hrestr : ∀ (σ : CLInternalTime RS) (ρ : CLInternalTime RT), restrT hS hT hi hU RU RT (E (σ, ρ)) = ρ := by
    intro σ ρ
    funext v
    exact hr σ ρ v.1 v.2
  have htT : ∀ (σ : CLInternalTime RS) (ρ : CLInternalTime RT), tT b RU ![t0, t1, t2] (E (σ, ρ)) = ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] := by
    intro σ ρ
    unfold tT
    rw [hclock σ ρ b hS.2.2.1]
    rfl
  refine ⟨E, hE, fun p σ ρ => ?_⟩
  have hlow : lowModC RU lam ![t0, t1, t2] (E (σ, ρ)) =
      lowModC RT lam ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ := by
    unfold lowModC
    have := clockT hS hT hi hU RU RT ![t0, t1, t2] (E (σ, ρ)) hT.2.2.1
    rw [hrestr σ ρ, htT σ ρ] at this
    rw [← this]
  have hfU : fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p (E (σ, ρ)) =
      spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
        clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
          ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] p.2 ρ := by
    unfold fU
    have e1 := spart_congr D hG L γ δ F layer hLayer base hS RS p.1.1 (fun v hv => hclock σ ρ v hv)
    have e2 : clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
        (tT b RU ![t0, t1, t2] (E (σ, ρ))) p.2 (restrT hS hT hi hU RU RT (E (σ, ρ))) =
        clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
          ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] p.2 ρ := by
      rw [hrestr σ ρ, htT σ ρ]
    exact congrArg₂ (· * ·) e1 e2
  unfold fUM
  refine (congrArg₂ (· * ·) hlow hfU).trans ?_
  ring

end Fubini

end WaveTurbulence.VineEstS5C.FlatMod
