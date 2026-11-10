/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse

/-! # FLAT-MOD (R60), the modulation as a factor of the summand, and the base case

`modPsi b lam Ψ x t u = e^{πiλ u_b} Ψ x t u`: the modulation carried inside the summand.  `lkRaw_modPsi`: `lkRaw R (modPsi b lam Ψ)` is the
`lkRaw` with the factor `Cont.lowModC R lam t τ` in the time integrand (the lower joint of `R` being `b`).
`Lvl.classSumM_base`: with no operative member the modulated class sum of a level is `c ζ lkRaw (modPsi b lam psiBase)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

variable {w : ℕ} {G : Garden w} {d : ℕ}

/-- The modulation `e^{πiλ u_b}` carried inside a summand. -/
noncomputable def modPsi (b : GBranch G.tree) (lam : ℝ) (Ψ : PsiT G d) : PsiT G d :=
  fun x t u => Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) * Ψ x t u

theorem lkRaw_modPsi {U : Finset (GBranch G.tree)} {a b b' : GBranch G.tree} (R : CLRegionData G U a b') (hb : b' = b)
    (lam : ℝ) (L : ℝ) (base : Mom d) (Ψ : PsiT G d) (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) :
    lkRaw R L base (modPsi b lam Ψ) t β =
      ∑' κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R,
        lowModC R lam t τ * Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) := by
  subst hb
  rfl

theorem clLocalKernelModC_eq_lkRaw {U : Finset (GBranch G.tree)} {a b b' : GBranch G.tree} (D : ReconstructionData G)
    (hG : G.IsPlain) (R : CLRegionData G U a b') (hb : b' = b) (lam L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) :
    clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base (modPsi b lam (psiNat D hG R L γ δ F layer hLayer base)) ![t0, t1, t2] ![e, f, g, h] := by
  rw [lkRaw_modPsi R hb]
  unfold clLocalKernelModC
  congr 1
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  rw [clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base _ _ κ τ]

variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **Base case, modulated**: with no operative member the modulated class sum of a level is the modulated native kernel. -/
theorem Lvl.classSumM_base (lam : ℝ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0)) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold Lvl.classSumM
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold twistedLocalKernelM
  exact clLocalKernelModC_eq_lkRaw _ _ lv.region lv.hcb lam _ _ _ _ _ _ _ _ _ _ _ _ _ _

end WaveTurbulence.VineEstS5C
