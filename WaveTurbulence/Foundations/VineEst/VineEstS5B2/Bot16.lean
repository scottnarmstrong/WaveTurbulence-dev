/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot15

/-! # V5 Step 4d-B2: the S-side twist identity at an operative BOTTOM vine

**`tildeJ2_bundle_bottom`** (TARGET Step 4, L1850-L1935, for `p* = ` the bottom piece, `U^{<p}` empty): for a state `A` with prime skeleton, a
chain region `c0` of `A` whose bottom joint is the lower joint of the member `pstar`, and no operation at any other member, the class sum
`∑_{y ∈ canonFinsetK p kind A c0} K^U_y` equals `c ζ ∑'_κ ∫_τ psiBot κ A c0 pstar (κ) t (clock τ)`, where
`psiBot x t u = ∑_{G} ε_G · frame_A · rowVal_G · bFac_A` is the A-chart bundle at the bottom vine: the exceptional pair rows `rowQ`, `rowT`
of every state `G` of the class, with the twisted clock slots and labels exchanged (`tw`), sign `ν_G`, and sign `ε_G = -1` for twisted
states; there is no lower factor (`K̃^{U<p}` is trivial: its only content, the conservation at `b` and the time conditions at the boundary
children, is the factor `bFac_A` and the boundary-decoration constraint of `CLLocalDecoration`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- The A-chart bundle at the bottom vine: the signed sum over the class of the integrands `stBot`. -/
@[expose] noncomputable def psiBot (p : ℕ) (kind : Bool) (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  ∑ z ∈ canonFinsetK p kind A c0, stBot κ A c0 pstar z.1 x t u

/-- Every state of the class `canonFinset` satisfies the per-state conclusion `BotGoal`. -/
theorem botGoal_of_mem (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {z : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hz : z ∈ canonFinsetK p kind A c0) :
    BotGoal κ A c0 pstar z := by
  obtain ⟨B, cB⟩ := z
  have hr := (mem_canonFinset_iff_bottom hA hup).mp hz
  rcases reach_single hr with e | ⟨op, e⟩
  · rw [e]
    exact botState_skip κ A c0 hb0 hL hF
  · rw [e]
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact botState_false κ A c0 hcan hel htc hcc hb0 con hL hF
    · exact botState_true κ A c0 hcan hel htc hcc hb0 con hL hF

/-- **The twisted factor identity at an operative bottom vine** (TARGET Step 4, `U^{<p}` empty).  The class sum of the kernels of the whole
chain region is `c ζ` times the local sum-integral of the A-chart bundle `psiBot`. -/
theorem tildeJ2_bundle_bottom (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ z ∈ canonFinsetK p kind A c0, twistedLocalKernel z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h], ∫ τ : CLInternalTime (botR A c0),
          psiBot p kind κ A c0 pstar (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) := by
  classical
  have hz := fun z (hz : z ∈ canonFinsetK p kind A c0) => botGoal_of_mem (p := p) κ A c0 hA hb0 hup hL hF hz
  rw [Finset.sum_congr rfl (fun z hz' => (hz z hz').1), ← Finset.mul_sum]
  congr 1
  have hint : ∀ κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h],
      ∫ τ : CLInternalTime (botR A c0), psiBot p kind κ A c0 pstar (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
          (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
        ∑ z ∈ canonFinsetK p kind A c0, ∫ τ : CLInternalTime (botR A c0),
          stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) := fun κd =>
    integral_finset_sum _ (fun z hz' => (hz z hz').2.1 κd)
  simp_rw [hint]
  exact (Summable.tsum_finsetSum (fun z hz' => Summable.of_norm_bounded (hz z hz').2.2
    (fun κd => norm_integral_le_integral_norm _))).symm

end WaveTurbulence.VineEstS5B2
