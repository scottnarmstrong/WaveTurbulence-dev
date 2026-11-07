/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotStateOps

/-! # FLAT-MOD (R60), the bottom vine: the modulated class sum (modulated `Bot16`, `Bot18`)

**`classSumM_bottom_state`**: `∑_{z ∈ canonFinset} K^{U,λ}_z = c ζ lkRaw (botR A c0) (modPsi b λ psiBot)`, the bottom case of the
modulated induction (`psiBot` unmodulated; the modulation is the factor `e^{πiλ u_b}`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

theorem botGoalM_of_mem (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {z : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hz : z ∈ canonFinsetK p kind A c0) :
    BotGoalM κ lam A c0 pstar z := by
  obtain ⟨B, cB⟩ := z
  have hr := (mem_canonFinset_iff_bottom hA hup).mp hz
  rcases reach_single hr with e | ⟨op, e⟩
  · rw [e]
    exact botStateM_skip κ lam A c0 hb0 hL hF
  · rw [e]
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact botStateM_false κ lam A c0 hcan hel htc hcc hb0 con hL hF
    · exact botStateM_true κ lam A c0 hcan hel htc hcc hb0 con hL hF

/-- **The modulated twisted factor identity at an operative bottom vine.** -/
theorem tildeJ2_bundle_bottomM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ z ∈ canonFinsetK p kind A c0, twistedLocalKernelM lam z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h], ∫ τ : CLInternalTime (botR A c0),
          lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          psiBot p kind κ A c0 pstar (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) := by
  classical
  have hz := fun z (hz : z ∈ canonFinsetK p kind A c0) => botGoalM_of_mem (p := p) (kind := kind) κ lam A c0 hA hb0 hup hL hF hz
  rw [Finset.sum_congr rfl (fun z hz' => (hz z hz').1), ← Finset.mul_sum]
  congr 1
  have hint : ∀ κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h],
      ∫ τ : CLInternalTime (botR A c0), lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          psiBot p kind κ A c0 pstar (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
          (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
        ∑ z ∈ canonFinsetK p kind A c0, ∫ τ : CLInternalTime (botR A c0),
          lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) := by
    intro κd
    have : ∀ τ : CLInternalTime (botR A c0), lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          psiBot p kind κ A c0 pstar (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
          (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
        ∑ z ∈ canonFinsetK p kind A c0, lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) := fun τ => by
      unfold psiBot; rw [Finset.mul_sum]
    simp_rw [this]
    exact integral_finset_sum _ (fun z hz' => (hz z hz').2.1 κd)
  simp_rw [hint]
  exact (Summable.tsum_finsetSum (fun z hz' => Summable.of_norm_bounded (hz z hz').2.2
    (fun κd => norm_integral_le_integral_norm _))).symm

/-- **The bottom case of the modulated induction over the core vines** (`b` the global lower joint, `c0.b = b`). -/
theorem classSumM_bottom_state (κ0 : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι)
    (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    ∑ z ∈ canonFinsetK p kind A c0, twistedLocalKernelM lam z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ0.L κ0.base ![e, f, g, h], ∫ τ : CLInternalTime (botR A c0),
          lowModC (botR A c0) lam ![t0, t1, t2] τ *
          psiBot p kind κ0 A c0 pstar (clExtendIndices (botR A c0) κd.1) ![t0, t1, t2]
            (clLocalClock (botR A c0) ![t0, t1, t2] τ) :=
  tildeJ2_bundle_bottomM (p := p) (kind := kind) { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h } lam A c0 hA hb0
    hup hL hF

end WaveTurbulence.VineEstS5C.FlatMod
