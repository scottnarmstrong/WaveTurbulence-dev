/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BotAbs3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs

/-! # Joint measurability of the bottom bundle `psiBot` (V5 Step 4d part C, 4d-B2 integration)

`measurable_bFac`, `measurable_botKernel`, **`measT_psiBot`**: `psiBot` is jointly measurable in the exterior times and the clock.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section BF
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

open Classical in
theorem measurable_bFac (R : CLRegionData G U a b) (L γ δ : ℝ) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => bFac R L γ δ base x z.1 z.2 := by
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have ht : ∀ j : Fin 3, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 j :=
    fun j => (measurable_pi_apply j).comp measurable_fst
  have hset : MeasurableSet {z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) | bTimeOK R z.1 z.2} := by
    unfold bTimeOK
    simp only [Set.ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · by_cases hP : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching
      · simp only [hP, true_implies]
        exact measurableSet_lt (ht 1) (hu b)
      · simp only [hP, false_implies, Set.ofPred_true]
        exact MeasurableSet.univ
    · by_cases hP : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching
      · simp only [hP, true_implies]
        exact measurableSet_lt (ht 2) (hu b)
      · simp only [hP, false_implies, Set.ofPred_true]
        exact MeasurableSet.univ
  unfold bFac
  exact (measurable_const.mul ((continuous_phaseAtom L γ δ (G.sign b.toNode) _).measurable.comp (hu b))).mul
    (Measurable.ite hset measurable_const measurable_const)

end BF

section Bot
variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

open Classical in
theorem measurable_botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    (hq : ∀ n : Fin d → ℤ, ∀ {f g : (Fin 3 → ℝ) × (GBranch A.skeleton.tree → ℝ) → ℝ}, Measurable f → Measurable g →
      Measurable fun z => rq (f z) (g z) (κ.base + latticePoint κ.L n))
    (hr : ∀ n : Fin d → ℤ, ∀ {f g : (Fin 3 → ℝ) × (GBranch A.skeleton.tree → ℝ) → ℝ}, Measurable f → Measurable g →
      Measurable fun z => rt (f z) (g z) (κ.base + latticePoint κ.L n))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) :
    Measurable fun z : (Fin 3 → ℝ) × (GBranch A.skeleton.tree → ℝ) => botKernel κ A c0 pstar tw ν rq rt x z.1 z.2 := by
  have hu : ∀ v : GBranch A.skeleton.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch A.skeleton.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have hHF := HF_of_all A.data A.plain κ.L κ.F (stateLayer A) κ.base hF
  unfold botKernel
  refine (measurable_spartFrame (u := fun z => z.2) hHF _ x hu).mul (Measurable.mul ?_ (measurable_bFac _ _ _ _ _ _))
  cases tw
  · exact measurable_rowVal ν rq rt _ _ (hq _) (hr _) (hu _) (hu _) (hu _)
  · exact measurable_rowVal ν rq rt _ _ (hq _) (hr _) (hu _) (hu _) (hu _)

open Classical in
/-- **`psiBot` is jointly measurable** in the exterior times and the clock. -/
theorem measT_psiBot (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    MeasT (psiBot p kind κ A c0 pstar) := by
  intro x
  unfold psiBot
  refine Finset.measurable_sum _ fun z _ => ?_
  unfold stBot
  refine measurable_const.mul (measurable_botKernel κ A c0 _ _ _ _ hF ?_ ?_ x)
  · intro n f g hf hg
    exact measurable_rowQ_comp κ z.1 pstar _ (couple_hF (HF_of_all z.1.data z.1.plain κ.L κ.F (stateLayer z.1) κ.base hF) _ n) hf hg
  · intro n f g hf hg
    exact measurable_rowT_comp κ z.1 pstar _
      (chain_hF (hLayer := stateLayer_isLayering z.1) (HF_of_all z.1.data z.1.plain κ.L κ.F (stateLayer z.1) κ.base hF) _ n) hf hg

end Bot

end WaveTurbulence.VineEstS5C
