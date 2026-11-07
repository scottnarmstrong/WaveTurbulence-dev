/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSb3
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final3

/-! # `SAbs` of the bundle `psiSB` (V5 Step 4d part C, `hAbs`, leaf `sb`)

`sAbs_bundle_state`: every state `G ∈ Zp(A)` has an `SAbs` bound for its bundle kernel (skip / FALSE / TRUE choice).  **`sAbs_psiSB`**: the signed
finite sum `psiSB` has an `SAbs` bound. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ}

open Classical in
theorem sAbs_bundle_state (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    ∃ C : ℝ, 0 ≤ C ∧ SAbs sp0.RS κ.L κ.base
      (fun x u => bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar) (rowQ κ G.1 pstar)
        (rowT κ G.1 pstar) x u) C := by
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    rw [decide_eq_false hn]
    exact ⟨_, baseConst_nonneg _, sAbs_bundle_skip κ A sp0 hL hF⟩
  | apply op h =>
    cases h
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · have hn := tw_false A hcan hel htc hcc con
      rw [decide_eq_false hn]
      exact ⟨_, baseConst_nonneg _, sAbs_bundle_false κ A sp0 hcan hel htc hcc con hL hF⟩
    · have ht := tw_true A hcan hel htc hcc con
      rw [decide_eq_true ht]
      exact ⟨_, baseConst_nonneg _, sAbs_bundle_true κ A sp0 hcan hel htc hcc con hL hF⟩

open Classical in
/-- **`SAbs` of the bundle `psiSB`.** -/
theorem sAbs_psiSB (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∃ CS : ℝ, 0 ≤ CS ∧ SAbs sp0.RS κ.L κ.base (psiSB (p := p) (kind := kind) κ A sp0 hA) CS := by
  have hh : ∀ G ∈ zpFinset p kind pstar J A sp0 hA, ∃ C : ℝ, 0 ≤ C ∧ SAbs sp0.RS κ.L κ.base
      (fun x u => epsOf A pstar G.1 * bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar)
        (rowQ κ G.1 pstar) (rowT κ G.1 pstar) x u) C := by
    intro G hG
    obtain ⟨C, hC0, hC⟩ := sAbs_bundle_state (p := p) (kind := kind) κ A sp0 hA hL hF hG
    exact ⟨‖epsOf A pstar G.1‖ * C, mul_nonneg (norm_nonneg _) hC0, sAbs_const_mul sp0.RS κ.L κ.base _ _ hC⟩
  choose! C hC0 hC using hh
  refine ⟨∑ G ∈ zpFinset p kind pstar J A sp0 hA, C G, Finset.sum_nonneg fun G hG => hC0 G hG, ?_⟩
  exact sAbs_finsetSum sp0.RS κ.L κ.base (zpFinset p kind pstar J A sp0 hA)
    (fun G x u => epsOf A pstar G.1 * bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar)
        (rowQ κ G.1 pstar) (rowT κ G.1 pstar) x u) C hC

end WaveTurbulence.VineEstS5C
