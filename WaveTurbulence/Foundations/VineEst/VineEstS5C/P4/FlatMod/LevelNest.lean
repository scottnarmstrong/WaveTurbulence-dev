/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Bundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec

/-! # FLAT-MOD (R60), one level of TARGET Step 4, nested form, for the modulated kernel

`Lvl.classSumM`: the class sum of a level with the modulated member kernels `twistedLocalKernelM`.  **`Lvl.classSumM_nested`**: the class
sum of a level is the S-side with the (unmodulated) bundle `psiSB` and the lower factor the modulated class sum of the next level.
(The modulation sits at the lower joint `b`, which is the lower joint of every level; it is carried by the lower factor.)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod

namespace FlatMod
variable {w : ℕ} {ι ι' : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

theorem kTM_eq_twistedLocalKernelM (κ : KPar d) (lam : ℝ) (X : FamilyReconstruction w ι)
    (sp : SplitAt X.skeleton X.family pstar J) (e : ι' → ι) (he : Function.Injective e) (hJ : ∀ j, e j ∈ J) (t : ℝ)
    (E F' : Mom d) :
    kTM κ lam X sp t E F' = twistedLocalKernelM lam (restrictState X e he) (chainOfSplit X sp e he hJ) κ.L κ.γ κ.δ κ.F κ.base t κ.t1
      κ.t2 E F' κ.g κ.h := by
  unfold kTM twistedLocalKernelM
  exact clLocalKernelModC_idx rfl sp.joint rfl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

section
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open Classical in
/-- **The common lower factor `K̃^λ` of the member `pstar` is the modulated class sum of the restricted problem.** -/
theorem KtilM_eq_canon (hc : Stage1.OpsCommute p kind w ι) (e : ι' → ι) (he : Function.Injective e)
    (hJ : ∀ j, e j ∈ J) (hJ' : ∀ i ∈ J, ∃ j, e j = i) (κ : KPar d) (lam : ℝ) {A : FamilyReconstruction w ι}
    (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) :
    KtilM (p := p) (kind := kind) κ lam A sp0 hA = fun t E F' =>
      ∑ z ∈ canonFinsetK p kind (restrictState A e he) (chainOfSplit A sp0 e he hJ),
        twistedLocalKernelM lam z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2 E F' κ.g κ.h := by
  funext t E F'
  rw [← sum_yA_eq_canon (g := fun X c => twistedLocalKernelM lam X c κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2 E F' κ.g κ.h)
    hc e he hJ hJ' hA sp0 hA0]
  unfold KtilM ktildeM
  refine Finset.sum_congr rfl fun y hy => ?_
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  unfold kTorM
  rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
  exact kTM_eq_twistedLocalKernelM κ lam y.1 y.2 e he hJ t E F'

end

section
variable [Fintype ι] [DecidableEq ι]

open Classical in
theorem sum_stIntM_eq (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : ExtS sp0.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp0.RS) :
    ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1 x σ =
      psiSB (p := p) (kind := kind) κ A sp0 hA x.1 (clLocalClock sp0.RS ![κ.t0, κ.t1, κ.t2] σ) *
        KtilM (p := p) (kind := kind) κ lam A sp0 hA (clLocalClock sp0.RS ![κ.t0, κ.t1, κ.t2] σ sp0.sb.b)
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode)) := by
  unfold psiSB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [stIntM, bundleInt_eq_kernel]
  ring

end

end FlatMod

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The modulated class sum of a level, with the dynamic parameters explicit. -/
noncomputable def Lvl.classSumM (lam : ℝ) (lv : Lvl B) (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    twistedLocalKernelM lam z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h

/-- **One level of TARGET Step 4, nested form, modulated.** -/
theorem Lvl.classSumM_nested (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x.1
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            (lv.next B RD hG layer hLayer pstar hk).classSumM (p := p) (kind := kind) B RD hG layer hLayer lam κ0
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ
                (lv.split B RD hG layer hLayer pstar hk).sb.b) t1 t2
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))
              g h := by
  classical
  set A' := lv.state B RD hG layer hLayer with hA'
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  let κ : KPar d := { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h }
  have hc : Stage1.OpsCommute p kind w lv.ι := Stage1.opsCommute_all
  have h1 := tildeJ2_canonM (p := p) (kind := kind) κ lam A' sp hprime hA0 hL hF
  have h2 := tildeJ2_bundleM (p := p) (kind := kind) κ lam A' sp hprime hA0 hL hF
  have hKt := KtilM_eq_canon (p := p) (kind := kind) hc (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ lam hprime sp hA0
  have e1 : Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime, sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A' sp hprime G) := h1
  rw [e1, h2]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  have hp' : IsPrimeGarden A'.skeleton := hprime
  rw [sum_stIntM_eq (p := p) (kind := kind) κ lam A' sp hp' x σ, hKt]
  congr 1

end WaveTurbulence.VineEstS5C
