/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Nest
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Bottom
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedMerge
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3

/-! # V5-SPACE-EXT: bond-weighted FLAT-MOD at all levels

`classSumB_flat`: for every level, the bond-weighted modulated class sum is `c ζ lkRaw` of the bond weight of the
level region times the UNWEIGHTED modulated flat summand `psiFuel`. The induction runs over the core vines exactly
as `VineSpaceK.classSumUpper_flat`, with the lower factor now the bond-weighted class sum of the next level (the
induction hypothesis itself). The weight of the next level region is moved through `psiStepSp` (it reads only
lower-block labels), and the upper and lower bond weights recombine into the weight of the union block
(`bondW_union`). -/

@[expose] public section
namespace WaveTurbulence.VineSpaceB
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C VineSpaceK

section Merge
variable {w : ℕ} {d : ℕ} {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

/-- **Flattening of one level with an arbitrary bounded upper weight.** -/
theorem flat_merge_W (κ0 : KPar d) (hL : κ0.L ≠ 0) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton)
    (mS : (GNode A.skeleton.tree → Fin d → ℤ) → ℂ) (M : ℝ) (hm : ∀ x, ‖mS x‖ ≤ M) (Ψ' : PsiT A.skeleton d)
    (Knext : ℝ → Mom d → Mom d → ℂ) (RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b)
    (RUx : CLRegionData A.skeleton sp.c.U sp.c.a sp.c.b) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hK : ∀ (t : ℝ) (E F' : Mom d), Knext t E F' =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RTx * clLocalZeta RTx *
        lkRaw RTx κ0.L κ0.base Ψ' ![t, t1, t2] ![E, F', g, h])
    (hlocS : ∀ x (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 A sp hprime x u = psiSB (p := p) (kind := kind) κ0 A sp hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.tb.U, u v = u' v) → Ψ' x t' u = Ψ' x t' u')
    (hAbs : GlueAbsConv sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ')) :
    (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ0.L κ0.base e f, ∫ σ : CLInternalTime sp.RS,
          mS x.1 * (psiSB (p := p) (kind := kind) κ0 A sp hprime x.1 (clLocalClock sp.RS ![t0, t1, t2] σ) *
            Knext (clLocalClock sp.RS ![t0, t1, t2] σ sp.sb.b)
              (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).retained.toNode))) =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RUx * clLocalZeta RUx *
        lkRaw RUx κ0.L κ0.base (spatialMul (fun x => mS (rA sp.RS x))
          (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ')) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hSlow := SplitAt.slow sp
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hSlow.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hSlow.keep, hSlow.lower]
    exact (A.family.placement pstar).child.symm
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  have hRTx : ∀ (t : Fin 3 → ℝ) (β : Fin 4 → Mom d), lkRaw RTx κ0.L κ0.base Ψ' t β = lkRaw sp.RT κ0.L κ0.base Ψ' t β :=
    fun t β => lkRaw_idx rfl sp.joint.symm rfl RTx sp.RT _ _ Ψ' t β
  have hrb : ∀ t β, lkRaw sp.RT κ0.L κ0.base Ψ' t β =
      lkRaw sp.RT κ0.L κ0.base (fun x t u => Ψ' (rB sp.RT x) t u) t β := by
    intro t β
    unfold lkRaw
    refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact congrArg (fun z => Ψ' z t (clLocalClock sp.RT t τ)) (rB_ext sp.RT κ.1).symm
  have hmerge := lkRaw_spatialMul_split sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h
    (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') (fun x u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u)
    (fun x t u => Ψ' (rB sp.RT x) t u) hL (glueFactors_psiStepSp (p := p) (kind := kind) κ0 hL A sp hprime Ψ' t0 t1 t2 e f g h)
    (fun x u u' hu => hlocS _ _ _ hu) (fun x t' u u' hu => hlocT _ _ _ _ hu) hAbs mS M hm
  have hpt : ∀ (x : ExtS sp.RS κ0.L κ0.base e f) (σ : CLInternalTime sp.RS),
      mS x.1 * (psiSB (p := p) (kind := kind) κ0 A sp hprime x.1 (clLocalClock sp.RS ![t0, t1, t2] σ) *
        Knext (clLocalClock sp.RS ![t0, t1, t2] σ sp.sb.b)
          (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).retained.toNode))) =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RTx * clLocalZeta RTx *
        ((mS (rA sp.RS x.1) * psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x.1)
            (clLocalClock sp.RS ![t0, t1, t2] σ)) *
          lkRaw sp.RT κ0.L κ0.base (fun x t u => Ψ' (rB sp.RT x) t u)
            ![clLocalClock sp.RS ![t0, t1, t2] σ sp.sb.b, t1, t2] (bdT sp.RT κ0.L κ0.base x.1 g h)) := by
    intro x σ
    rw [hK, rA_of_free sp.RS x.2.1.1, ← hrb, ← hRTx]
    have hbd : bdT sp.RT κ0.L κ0.base x.1 g h =
        ![κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).lower.toNode),
          κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).retained.toNode), g, h] := by
      unfold bdT
      rw [hb0, hb1, hn0, hn1]
    rw [hbd]
    ring
  have hn1U : clLocalOrder1 RUx = clLocalOrder1 sp.RS + clLocalOrder1 sp.RT := by
    rw [clLocalOrder1_idx sp.union sp.sa.symm sp.tbb.symm RUx sp.RU]
    exact order1_split sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT
  have hzU : clLocalZeta RUx = clLocalZeta sp.RS * clLocalZeta sp.RT := by
    rw [clLocalZeta_idx sp.union sp.sa.symm sp.tbb.symm RUx sp.RU]
    exact zeta_split sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT
  have hnT : clLocalOrder1 RTx = clLocalOrder1 sp.RT := clLocalOrder1_idx rfl sp.joint.symm rfl RTx sp.RT
  have hzT : clLocalZeta RTx = clLocalZeta sp.RT := clLocalZeta_idx rfl sp.joint.symm rfl RTx sp.RT
  have hU2 : lkRaw RUx κ0.L κ0.base
      (spatialMul (fun x => mS (rA sp.RS x)) (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ'))
      ![t0, t1, t2] ![e, f, g, h] =
      lkRaw sp.RU κ0.L κ0.base
        (spatialMul (fun x => mS (rA sp.RS x)) (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ'))
        ![t0, t1, t2] ![e, f, g, h] :=
    lkRaw_idx sp.union sp.sa.symm sp.tbb.symm RUx sp.RU _ _ _ _ _
  rw [hU2, hmerge, hn1U, hzU, ← hnT, ← hzT]
  simp_rw [hpt]
  simp_rw [integral_const_mul]
  rw [tsum_mul_left, pow_add]
  ring

/-- Spatial multiplication commutes with the modulation. -/
theorem spatialMul_modPsi {G : Garden w} (m : (GNode G.tree → Fin d → ℤ) → ℂ) (b : GBranch G.tree) (lam : ℝ)
    (Ψ : PsiT G d) : spatialMul m (modPsi b lam Ψ) = modPsi b lam (spatialMul m Ψ) := by
  funext x t u
  simp only [spatialMul, modPsi]
  ring

/-- A spatial weight of the lower block passes through the split summand. -/
theorem psiStepSp_spatialMul (κ0 : KPar d) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton)
    (m : (GNode A.skeleton.tree → Fin d → ℤ) → ℂ) (Ψ' : PsiT A.skeleton d) :
    psiStepSp (p := p) (kind := kind) κ0 A sp hprime (spatialMul m Ψ') =
      spatialMul (fun x => m (rB sp.RT x)) (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') := by
  funext x t u
  simp only [psiStepSp, spatialMul]
  ring

/-- The modulation at a lower-block clock passes through the split summand. -/
theorem psiStepSp_modPsi (κ0 : KPar d) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton)
    (b : GBranch A.skeleton.tree) (lam : ℝ) (Ψ' : PsiT A.skeleton d) :
    psiStepSp (p := p) (kind := kind) κ0 A sp hprime (modPsi b lam Ψ') =
      modPsi b lam (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') := by
  funext x t u
  simp only [psiStepSp, modPsi]
  ring

/-- Recombine an upper and a lower spatial weight around the modulation. -/
theorem spatialMul_combine {G' : Garden w} (mU mS mT : (GNode G'.tree → Fin d → ℤ) → ℂ)
    (fS fT : (GNode G'.tree → Fin d → ℤ) → (GNode G'.tree → Fin d → ℤ)) (b : GBranch G'.tree) (lam : ℝ)
    (Ψ : PsiT G' d) (h : ∀ x, mU x = mS (fS x) * mT (fT x)) :
    spatialMul (fun x => mS (fS x)) (modPsi b lam (spatialMul (fun x => mT (fT x)) Ψ)) =
      spatialMul mU (modPsi b lam Ψ) := by
  funext x t u
  simp only [spatialMul, modPsi]
  rw [h x]
  ring

end Merge

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The bond weight of a level region, on the representative chart. -/
noncomputable def lvW (ψ : ℕ → ℕ → Mom d → ℂ) (κ0 : KPar d) (lv : Lvl B) : (GNode G.tree → Fin d → ℤ) → ℂ :=
  bW ψ κ0 (lv.state B RD hG layer hLayer) lv.c.U

/-- The base case: no operative member. -/
theorem classSumB_base (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv)
          (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0))) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold classSumB
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold memberB
  have hh := memberMX_eq_lkRaw (lv.state B RD hG layer hLayer).data
    (lv.state B RD hG layer hLayer).plain lv.region lam κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering _) κ0.base
    (lvW B RD hG layer hLayer ψ κ0 lv) t0 t1 t2 e f g h
  have hb : modPsi lv.c.b lam (lv.psiBase B RD hG layer hLayer κ0) =
      modPsi b lam (lv.psiBase B RD hG layer hLayer κ0) := by rw [lv.hcb]
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

/-- The bottom case: one operative bottom vine. -/
theorem classSumB_bottom (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv)
            (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)))
          ![t0, t1, t2] ![e, f, g, h] := by
  let κ : KPar d := {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h}
  have hh := sum_memberB_bottom_eq_flat (p := p) (kind := kind) κ lam ψ C hC hψ
    (lv.state B RD hG layer hLayer) lv.c hprime
    (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  have hb : modPsi lv.c.b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ (lv.state B RD hG layer hLayer) lv.c pstar) =
      modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) := by
    rw [lv.hcb]
    rfl
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

/-- **One level, flat form, bond-weighted.** -/
theorem classSumB_flat_step (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (Ψ' : PsiT G d)
    (hIH : ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
          t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region *
          clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
          lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base
            (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (modPsi b lam Ψ'))
            ![t0, t1, t2] ![e, f, g, h])
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U, u v = u' v) →
      Ψ' x t' u = Ψ' x t' u')
    (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hAbs : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
      (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) :
    classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv)
            (modPsi b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ')) =
      modPsi b lam (spatialMul (fun x => (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x))
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) := by
    exact (psiStepSp_modPsi κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime b lam _).trans
      (congrArg (modPsi b lam) (psiStepSp_spatialMul κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U := Lvl.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [classSumB_nested (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar hk hA0
    t0 t1 t2 e f g h]
  have hAbs' : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))) := by
    rw [hcomm]
    refine glueAbsConv_modPsi _ _ _ κ0.L κ0.base t0 t1 t2 e f g h _ ?_ b lam
    exact glueAbsConv_spatialMul (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h _ hAbs
      (fun x => (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x)) (C ^ (regionDarts G (lv.split B RD hG layer hLayer pstar hk).tb.U).card)
      (fun x => norm_bW_le ψ κ0 ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C hψ _)
  have hmerge := flat_merge_W (p := p) (kind := kind) κ0 hL (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (bW ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U)
    (C ^ (regionDarts G (lv.split B RD hG layer hLayer pstar hk).sb.U).card) (fun x => norm_bW_le ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U C hψ x)
    (modPsi b lam (spatialMul (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
    (fun t E F' => classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk)
      κ0 t t1 t2 E F' g h)
    (lv.next B RD hG layer hLayer pstar hk).region lv.region t0 t1 t2 e f g h
    (fun t E F' => (hIH t t1 t2 E F' g h).trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^
      clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region * clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
      lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base Ψ ![t, t1, t2] ![E, F', g, h]) (spatialMul_modPsi _ _ _ _))) hlocS
    (fun x t' u u' hu => by
      unfold modPsi spatialMul
      rw [hu b hbT, hlocT x t' u u' hu])
    hAbs'
  have hcU : lv.c.U = (lv.split B RD hG layer hLayer pstar hk).sb.U ∪ (lv.split B RD hG layer hLayer pstar hk).tb.U := (lv.split B RD hG layer hLayer pstar hk).union
  have hw : ∀ x : GNode G.tree → Fin d → ℤ, lvW B RD hG layer hLayer ψ κ0 lv x =
      bW ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x) * (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    unfold lvW bW
    rw [hcU, bondW_union ψ κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU x,
      bondW_rA ψ κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RS x]
    congr 1
    exact (bondW_rB ψ κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RT x).symm
  have hΨ := spatialMul_combine (G' := G) (lvW B RD hG layer hLayer ψ κ0 lv) (bW ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U) (lvW B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk))
    (rA (lv.split B RD hG layer hLayer pstar hk).RS) (rB (lv.split B RD hG layer hLayer pstar hk).RT) b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') hw
  refine hmerge.trans ((congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region *
    clLocalZeta lv.region * lkRaw lv.region κ0.L κ0.base
      (spatialMul (fun x => bW ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x)) Ψ) ![t0, t1, t2] ![e, f, g, h]) hcomm).trans ?_)
  exact congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base Ψ ![t0, t1, t2] ![e, f, g, h]) hΨ

open Classical in
/-- **The bond-weighted modulated induction over the core vines.** -/
theorem classSumB_flat (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : Lvl B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv)
              (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv)))
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  induction m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [classSumB_base (p := p) (kind := kind) B RD hG layer hLayer lam ψ κ0 hprime lv hno]
    simp only [Lvl.psiFuel, hnop, dite_false]
  | succ m ih =>
    intro lv hc t0 t1 t2 e f g h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
      set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      swap
      · have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dite_eq_left hop]
          exact dite_eq_right hk
        rw [hstep]
        exact classSumB_bottom (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar h0 hup
          t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := Lvl.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => ih (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Lvl.psiFuel, dite_eq_left hop]
        exact dite_eq_left hk
      rw [hstep]
      exact classSumB_flat_step (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar hk hA0 _
        hIH (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [classSumB_base (p := p) (kind := kind) B RD hG layer hLayer lam ψ κ0 hprime lv hno]
      simp only [Lvl.psiFuel, hop, dite_false]

/-- **Bond-weighted FLAT-MOD**: every level's bond-weighted class sum is `c ζ lkRaw` of the level's bond weight
times the unweighted modulated `psiFuel`. -/
theorem classSumB_eq_flat (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvW B RD hG layer hLayer ψ κ0 lv)
            (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv)))
          ![t0, t1, t2] ![e, f, g, h] :=
  classSumB_flat (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime
    (fun lv pstar hk x _u _u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t _u _u' hu => Lvl.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (Lvl.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime
      (Lvl.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h

end WaveTurbulence.VineSpaceB
