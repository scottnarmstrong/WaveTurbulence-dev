/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec

/-! # Flattening one level of the induction over the core vines (V5 Step 4d part C, WP-I)

`PsiT`: abstract clock-based summands.  `psiStepSp κ0 A sp hprime Ψ'`: the summand of the split `sp` below which the lower factor
has the summand `Ψ'` (`psiSB` of the restricted decoration times `Ψ'` of the decoration restricted to the support of the lower block,
at the exterior times `(u b, t1, t2)`).  `glueFactors_psiStepSp`, **`flat_merge`**: the S-side with the bundle and a lower factor
`c ζ lkRaw Ψ'` is `c ζ lkRaw (psiStepSp Ψ')` of the whole region (via `lkRaw_split_fubini`; hypotheses: clock locality of the bundle and of `Ψ'`,
absolute convergence of the glued summands).  **`Lvl.classSum_flat_step`**: the class sum of a level is `c ζ lkRaw R (Lvl.psiStep Ψ')` given
the same for the next level.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {d : ℕ} {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

/-- The type of an abstract summand. -/
abbrev PsiT (G : Garden w) (d : ℕ) : Type :=
  (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ

theorem rB_ext {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (z : ↥(clLocalSupport R) → (Fin d → ℤ)) : rB R (clExtendIndices R z) = clExtendIndices R z := by
  funext y
  unfold rB
  by_cases hy : y ∈ clLocalSupport R
  · simp [hy]
  · simp [hy, clExtendIndices_of_notMem R z hy]

theorem rA_of_free {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    {x : GNode G.tree → (Fin d → ℤ)} (hx : ∀ y, y ∉ splitA RS → x y = 0) : rA RS x = x := by
  funext y
  unfold rA
  by_cases hy : y ∈ splitA RS
  · simp [hy]
  · simp [hy, hx y hy]

theorem clLocalOrder1_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a')
    (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') : clLocalOrder1 R = clLocalOrder1 R' := by
  subst hU ha hb; rw [regionData_subsingleton R R']

theorem clLocalZeta_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a')
    (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') : clLocalZeta R = clLocalZeta R' := by
  subst hU ha hb; rw [regionData_subsingleton R R']

/-- The summand of a split: the bundle times the lower summand. -/
noncomputable def psiStepSp (κ0 : KPar d) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton) (Ψ' : PsiT A.skeleton d) :
    PsiT A.skeleton d :=
  fun x t u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u * Ψ' (rB sp.RT x) ![u sp.sb.b, t 1, t 2] u


theorem glueFactors_psiStepSp (κ0 : KPar d) (hL : κ0.L ≠ 0) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton) (Ψ' : PsiT A.skeleton d)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    GlueFactors sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ')
      (fun x u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u) (fun x t u => Ψ' (rB sp.RT x) t u) := by
  intro p' τ
  have hc := (clExtEquiv sp.RT κ0.L κ0.base _ p'.2).2.2
  have hrA : rA sp.RS (glue sp.RS p'.1.1 (clExtendIndices sp.RT p'.2.1)) = rA sp.RS p'.1.1 := by
    funext y
    unfold rA glue
    by_cases hy : y ∈ splitA sp.RS <;> simp [hy]
  have hrB : rB sp.RT (glue sp.RS p'.1.1 (clExtendIndices sp.RT p'.2.1)) = clExtendIndices sp.RT p'.2.1 := by
    conv_rhs => rw [← rB_ext sp.RT p'.2.1]
    funext y
    unfold rB
    by_cases hy : y ∈ clLocalSupport sp.RT
    · simp only [hy, ite_true]
      exact glue_B sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT hL (xT := clExtendIndices sp.RT p'.2.1) hc hy
    · simp [hy]
  unfold fGlue
  simp only [psiStepSp, hrA, hrB, tT, rB_ext]


/-- **Flattening of one level**: the S-side with the bundle and a lower factor of `lkRaw` form is the `lkRaw` of the glued summand. -/
theorem flat_merge (κ0 : KPar d) (hL : κ0.L ≠ 0) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hprime : IsPrimeGarden A.skeleton) (Ψ' : PsiT A.skeleton d)
    (Knext : ℝ → Mom d → Mom d → ℂ) (RTx : CLRegionData A.skeleton sp.tb.U sp.tb.a sp.tb.b)
    (RUx : CLRegionData A.skeleton sp.c.U sp.c.a sp.c.b) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hK : ∀ (t : ℝ) (E F' : Mom d), Knext t E F' =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RTx * clLocalZeta RTx *
        lkRaw RTx κ0.L κ0.base Ψ' ![t, t1, t2] ![E, F', g, h])
    (hlocS : ∀ x (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 A sp hprime x u = psiSB (p := p) (kind := kind) κ0 A sp hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch A.skeleton.tree → ℝ), (∀ v ∈ sp.tb.U, u v = u' v) → Ψ' x t' u = Ψ' x t' u')
    (hAbs : GlueAbsConv sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ')) :
    (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ0.L κ0.base e f, ∫ σ : CLInternalTime sp.RS,
          psiSB (p := p) (kind := kind) κ0 A sp hprime x.1 (clLocalClock sp.RS ![t0, t1, t2] σ) *
            Knext (clLocalClock sp.RS ![t0, t1, t2] σ sp.sb.b)
              (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).retained.toNode)) =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RUx * clLocalZeta RUx *
        lkRaw RUx κ0.L κ0.base (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hS := sp.sb.block
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
  have hmerge := lkRaw_split_fubini sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT κ0.L κ0.base t0 t1 t2 e f g h
    (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') (fun x u => psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x) u)
    (fun x t u => Ψ' (rB sp.RT x) t u) hL (glueFactors_psiStepSp (p := p) (kind := kind) κ0 hL A sp hprime Ψ' t0 t1 t2 e f g h)
    (fun x u u' hu => hlocS _ _ _ hu) (fun x t' u u' hu => hlocT _ _ _ _ hu) hAbs
  have hpt : ∀ (x : ExtS sp.RS κ0.L κ0.base e f) (σ : CLInternalTime sp.RS),
      psiSB (p := p) (kind := kind) κ0 A sp hprime x.1 (clLocalClock sp.RS ![t0, t1, t2] σ) *
        Knext (clLocalClock sp.RS ![t0, t1, t2] σ sp.sb.b)
          (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x.1 (A.family.placement pstar).retained.toNode)) =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 RTx * clLocalZeta RTx *
        (psiSB (p := p) (kind := kind) κ0 A sp hprime (rA sp.RS x.1) (clLocalClock sp.RS ![t0, t1, t2] σ) *
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
  have hU2 : lkRaw RUx κ0.L κ0.base (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') ![t0, t1, t2] ![e, f, g, h] =
      lkRaw sp.RU κ0.L κ0.base (psiStepSp (p := p) (kind := kind) κ0 A sp hprime Ψ') ![t0, t1, t2] ![e, f, g, h] :=
    lkRaw_idx sp.union sp.sa.symm sp.tbb.symm RUx sp.RU _ _ _ _ _
  rw [hU2, hmerge, hn1U, hzU, ← hnT, ← hzT]
  simp_rw [hpt]
  simp_rw [integral_const_mul]
  rw [tsum_mul_left, pow_add]
  ring


section LvlStep
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The summand of a level below which the lower level has the summand `Ψ'`. -/
noncomputable def Lvl.psiStep (κ0 : KPar d) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hprime : IsPrimeGarden G) (Ψ' : PsiT G d) : PsiT G d :=
  psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime Ψ'

end LvlStep

end WaveTurbulence.VineEstS5C
