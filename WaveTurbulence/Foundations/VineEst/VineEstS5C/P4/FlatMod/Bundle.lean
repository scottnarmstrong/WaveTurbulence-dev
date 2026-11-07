/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final3

/-! # FLAT-MOD (R60), the twisted factor identity at `U^p` for the modulated kernels

`KtilM`, `ktildeM_eq`, `ktildeM_sum`, `sok_ktildeM`, `stIntM`, `zp_stateM` and **`tildeJ2_bundleM`**: the modulated
`VineEstS5B.Ktil` ... `tildeJ2_bundle` (Final2, Final3).  The rows enter only through `rowQ`, `rowT`, `nuOf`, `epsOf` and
`bundleInt`, which do not see the modulation (it sits in the lower factor `KtilM`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The common lower factor `K̃_T` at the state `A`. -/
noncomputable def KtilM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) : ℝ → Mom d → Mom d → ℂ :=
  ktildeM (p := p) (kind := kind) κ lam A sp0 hA ⟨A, sp0⟩

open Classical in
theorem ktildeM_eq (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) :
    ktildeM (p := p) (kind := kind) κ lam A sp0 hA G = fun t E F' =>
      if twAt A G.1 pstar then KtilM (p := p) (kind := kind) κ lam A sp0 hA t F' E else KtilM (p := p) (kind := kind) κ lam A sp0 hA t E F' := by
  classical
  funext t E F'
  have hnA : ¬ twAt A A pstar := not_twAt_of_eq rfl
  simp only [KtilM, ktildeM, kTorM]
  by_cases htw : twAt A G.1 pstar
  · simp only [htw, hnA, if_true, if_false]
  · simp only [htw, hnA, if_false]

theorem ktildeM_sum (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    ktildeM (p := p) (kind := kind) κ lam A sp0 hA G = fun t E F' => ∑ x ∈ yFinset p kind pstar J A sp0 hA G, kTM κ lam x.1 x.2 t E F' := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  funext t E F'
  unfold ktildeM
  refine (sum_yG_eq_yA hc hA hG (fun x => kTM κ lam x.1 x.2 t E F') (fun y => kTorM κ lam A G.1 pstar y t E F') ?_).symm
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kTM_rel κ lam hA hr hM hMy hxr hyr hxy t E F'

theorem sok_ktildeM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    SOKAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kTM κ lam x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kTM κ lam x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF))
  rw [ktildeM_sum κ lam A sp0 hA hG]
  exact sok_sum G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1) (stateLayer_isLayering G.1) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept) (yFinset p kind pstar J A sp0 hA G)
    (fun x t E F' => kTM κ lam x.1 x.2 t E F') hsok


open Classical in
/-- The integrand of the state `G` in the chart of `A`. -/
noncomputable def stIntM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : FamilyReconstruction w ι)
    (x : ExtS sp0.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp0.RS) : ℂ :=
  epsOf A pstar G * bundleInt κ A sp0 (KtilM (p := p) (kind := kind) κ lam A sp0 hA) (decide (twAt A G pstar)) (nuOf G pstar)
    (rowQ κ G pstar) (rowT κ G pstar) x σ


theorem zp_stateM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        (∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS, stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1 x σ) ∧
    BOK sp0.RS κ.L κ.base κ.e κ.f (stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1) := by
  classical
  have hok := sok_ktildeM κ lam A sp0 hA hA0 hL hF hG
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hok hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    have e : stIntM (p := p) (kind := kind) κ lam A sp0 hA A = bundleInt κ A sp0 (KtilM (p := p) (kind := kind) κ lam A sp0 hA) false (nuOf A pstar)
        (rowQ κ A pstar) (rowT κ A pstar) := by
      funext x σ; simp [stIntM, epsOf, hn]
    rw [e]
    exact ⟨sSumAt_skip κ A sp0 _, bok_skip κ A sp0 _ hok⟩
  | apply op h =>
    cases h
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · have hn := tw_false A hcan hel htc hcc con
      have hk : ktildeM (p := p) (kind := kind) κ lam A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar false⟩ = KtilM (p := p) (kind := kind) κ lam A sp0 hA := by
        rw [ktildeM_eq]; funext t E F'; simp [hn]
      have e : stIntM (p := p) (kind := kind) κ lam A sp0 hA (opOut A pstar hcan hel htc hcc con) =
          bundleInt κ A sp0 (KtilM (p := p) (kind := kind) κ lam A sp0 hA) false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) := by
        funext x σ; simp [stIntM, epsOf, hn]
      rw [hk] at hok ⊢
      rw [e]
      exact ⟨sSumAt_false κ A sp0 hcan hel htc hcc con _, bok_false κ A sp0 hcan hel htc hcc con _ hok⟩
    · have ht := tw_true A hcan hel htc hcc con
      have hk : ktildeM (p := p) (kind := kind) κ lam A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar true⟩ =
          fun t E F' => KtilM (p := p) (kind := kind) κ lam A sp0 hA t F' E := by
        rw [ktildeM_eq]; funext t E F'; simp [ht]
      have e : stIntM (p := p) (kind := kind) κ lam A sp0 hA (opOut A pstar hcan hel htc hcc con) = fun x σ =>
          -bundleInt κ A sp0 (fun t E Fr => (fun t E F' => KtilM (p := p) (kind := kind) κ lam A sp0 hA t F' E) t Fr E) true
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
        funext x σ; simp [stIntM, epsOf, ht]
      rw [hk] at hok ⊢
      rw [e]
      refine ⟨?_, ?_⟩
      · rw [sSumAt_true κ A sp0 hcan hel htc hcc con]
        simp only [integral_neg, tsum_neg]
        ring
      · obtain ⟨h1, h2⟩ := bok_true κ A sp0 hcan hel htc hcc con _ hok
        exact ⟨fun x => (h1 x).neg, by simpa [norm_neg] using h2⟩

/-- **The twisted factor identity at `U^p`** (TARGET `(tildeJ2)` with the sum over the LF twists at `p*` carried inside the
decoration sum and the time integral of the chart of `A`). -/
theorem tildeJ2_bundleM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ G ∈ zpFinset p kind pstar J A sp0 hA, sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        ∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS,
          ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1 x σ := by
  classical
  have hz := fun G (hG : G ∈ zpFinset p kind pstar J A sp0 hA) => zp_stateM κ lam A sp0 hA hA0 hL hF hG
  rw [Finset.sum_congr rfl (fun G hG => (hz G hG).1), ← Finset.mul_sum]
  congr 1
  have hint : ∀ x, ∫ σ, ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1 x σ =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, ∫ σ, stIntM (p := p) (kind := kind) κ lam A sp0 hA G.1 x σ := fun x =>
    integral_finset_sum _ (fun G hG => (hz G hG).2.1 x)
  simp_rw [hint]
  exact (Summable.tsum_finsetSum (fun G hG => Summable.of_norm_bounded (hz G hG).2.2
    (fun x => norm_integral_le_integral_norm _))).symm


end WaveTurbulence.VineEstS5C.FlatMod
