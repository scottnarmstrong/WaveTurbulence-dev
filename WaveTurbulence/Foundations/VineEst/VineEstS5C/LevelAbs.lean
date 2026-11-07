/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsGlue3

/-! # `hAbs` by induction on the levels: the reduction to the S-side bound and the base bound (V5 Step 4d part C)

`MeasT Ψ`: joint measurability of a summand in the exterior times and the clock.  `Lvl.absStep`: if the lower summand `Ψ'` has a uniform
`UAbs` bound on the next level and is jointly measurable, and the bundle `psiSB` has a `SAbs` bound and is measurable, then `Lvl.psiStep Ψ'` has a
uniform `UAbs` bound on the level, is jointly measurable, and its glued summands converge absolutely (`GlueAbsConv`, the hypothesis `hAbs` of
`Lvl.classSum_flat`).  `Lvl.absFuel`: the induction over the fuel from the base bound of `psiBase`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- Joint measurability of an abstract summand in the exterior times and the clock. -/
def MeasT (Ψ : PsiT G d) : Prop :=
  ∀ x, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => Ψ x z.1 z.2

theorem measurable_extVec (b : GBranch G.tree) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => (![z.2 b, z.1 1, z.1 2] : Fin 3 → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · exact (measurable_pi_apply b).comp measurable_snd
  · show Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 1
    exact (measurable_pi_apply (1 : Fin 3)).comp measurable_fst
  · show Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 2
    exact (measurable_pi_apply (2 : Fin 3)).comp measurable_fst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

theorem measT_psiStepSp (κ0 : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (hprime : IsPrimeGarden A.skeleton) (Ψ' : PsiT A.skeleton d)
    (hmS : ∀ x, Measurable (psiSB (p := p) (kind := kind) κ0 A sp hprime x)) (hm : MeasT Ψ') :
    MeasT (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') := fun x =>
  ((hmS _).comp measurable_snd).mul ((hm _).comp ((measurable_extVec sp.sb.b).prodMk measurable_snd))


section StepSp
variable (κ0 : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
  (hprime : IsPrimeGarden A.skeleton) (Ψ' : PsiT A.skeleton d)

/-- Common hypotheses of the glue at a split. -/
structure StepHyp {CS CT : ℝ} (RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b) : Prop where
  hlocS : ∀ x (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.sb.U, u v = u' v) →
    psiSB (p := p) (kind := kind) κ0 A sp hprime x u = psiSB (p := p) (kind := kind) κ0 A sp hprime x u'
  hlocT : ∀ x t' (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.tb.U, u v = u' v) → Ψ' x t' u = Ψ' x t' u'
  hmS : ∀ x, Measurable (psiSB (p := p) (kind := kind) κ0 A sp hprime x)
  hm : MeasT Ψ'
  hS : SAbs sp.RS κ0.L κ0.base (psiSB (p := p) (kind := kind) κ0 A sp hprime) CS
  hT : UAbs RTx κ0.L κ0.base Ψ' CT
  hCT : 0 ≤ CT

theorem StepHyp.glue {CS CT : ℝ} {RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b}
    (hL : κ0.L ≠ 0) (H : StepHyp (p := p) (kind := kind) κ0 A sp hprime Ψ' (CS := CS) (CT := CT) RTx) :
    (∀ t0 t1 t2 e f g h, GlueFactors sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') (fun x u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u)
      (fun x t u => Ψ' (rB sp.RT x) t u)) ∧
    SAbs sp.RS κ0.L κ0.base (fun x u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u) CS ∧
    UAbs sp.RT κ0.L κ0.base (fun x t u => Ψ' (rB sp.RT x) t u) CT := by
  refine ⟨fun t0 t1 t2 e f g h => glueFactors_psiStepSp (p := p) (kind := kind) κ0 hL A sp hprime Ψ' t0 t1 t2 e f g h, ?_, ?_⟩
  · refine (sAbs_congr sp.RS κ0.L κ0.base _ _ CS (fun x e f hx u => ?_)).mp H.hS
    obtain ⟨y, rfl⟩ := hx
    rw [rA_of_free sp.RS y.2.1.1]
  · refine (uAbs_congr sp.RT κ0.L κ0.base Ψ' _ CT (fun z t u => ?_)).mp
      ((uAbs_idx rfl sp.joint.symm rfl RTx sp.RT κ0.L κ0.base Ψ' CT).mp H.hT)
    rw [rB_ext]

/-- **`UAbs` of the glued summand at a split.** -/
theorem StepHyp.uAbs {CS CT : ℝ} {RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b}
    (RUx : CLRegionData A.skeleton sp.c.U sp.c.a sp.c.b)
    (hL : κ0.L ≠ 0) (H : StepHyp (p := p) (kind := kind) κ0 A sp hprime Ψ' (CS := CS) (CT := CT) RTx) :
    UAbs RUx κ0.L κ0.base (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') (CS * CT) := by
  obtain ⟨hfac, hS, hT⟩ := StepHyp.glue κ0 A sp hprime Ψ' hL H
  refine (uAbs_idx sp.union sp.sa.symm sp.tbb.symm RUx sp.RU κ0.L κ0.base _ _).mpr ?_
  exact uAbs_glue sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT κ0.L κ0.base _ _ _ hL hfac
    (fun x u u' hu => H.hlocS _ _ _ hu) (fun x t' u u' hu => H.hlocT _ _ _ _ hu)
    (fun _ => H.hmS _) (fun _ => H.hm _) H.hCT hS hT

/-- **Absolute convergence of the glued summands at a split** (`hAbs` of `Lvl.classSum_flat`). -/
theorem StepHyp.glueAbsConv {CS CT : ℝ} {RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b}
    (hL : κ0.L ≠ 0) (H : StepHyp (p := p) (kind := kind) κ0 A sp hprime Ψ' (CS := CS) (CT := CT) RTx) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    GlueAbsConv sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') := by
  obtain ⟨hfac, hS, hT⟩ := StepHyp.glue κ0 A sp hprime Ψ' hL H
  exact (glueAbs_of_bounds sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h _ _ _
    (hfac t0 t1 t2 e f g h) (fun x u u' hu => H.hlocS _ _ _ hu) (fun x t' u u' hu => H.hlocT _ _ _ _ hu)
    (fun _ => H.hmS _) (fun _ => H.hm _) H.hCT hS hT).1

end StepSp

end WaveTurbulence.VineEstS5C
