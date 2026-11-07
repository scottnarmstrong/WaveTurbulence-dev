/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotKernel

/-! # FLAT-MOD (R60), the bottom vine, states of the class (modulated `Bot11`-`Bot14`)

`BotGoalM`: the modulated per-state conclusion, `K^{U,λ}_z = c ζ ∑' ∫ lowModC · stBot`, with `BOKd`.  `botStateM_skip`, `botStateM_false`,
`botStateM_true`: the three kinds of state reached by a batch over the bottom member.  The pointwise identities (`stBot` against the
summand of the state, `hint` / `hpt`) are those of `Bot11`-`Bot14`; the modulation is a common factor (`lowModC_tw` at the twisted state).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- The modulated per-state conclusion: the modulated kernel of the state at its chain region is `c ζ ∑' ∫ lowModC · stBot` in the chart of `A`. -/
def BotGoalM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (z : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) : Prop :=
  twistedLocalKernelM lam z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h], ∫ τ : CLInternalTime (botR A c0),
          lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
          stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) ∧
    BOKd (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h] fun κd τ =>
      lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
      stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)

open Classical in
theorem botStateM_skip (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoalM κ lam A c0 pstar ⟨A, c0⟩ := by
  have hS := chain_slow c0 pstar hb0
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  have hint : ∀ (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)),
      stBot κ A c0 pstar A (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      clLocalSummand A.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base
        ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := by
    intro κd τ
    have hFree : FreeDec (botR A c0) (clExtendIndices (botR A c0) κd.1) :=
      ⟨fun y hy => clExtendIndices_of_notMem _ _ hy, κd.2.1, κd.2.2.1⟩
    have hpx : PairedAt (A.family.placement pstar) (clExtendIndices (botR A c0) κd.1) :=
      hFree.2.2 _ hS.retained_internal
    rw [summand_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
      (stateLayer_isLayering A) κ.base (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
      hS.b_mem_erase hS.p0_mem (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _)]
    rw [sameIntB_eq_botKernel κ A c0 hb0 A A.data (stateLayer A) (stateLayer_isLayering A) rfl rfl rfl _ hpx]
    unfold stBot epsOf
    have hd : decide (twAt A A pstar) = false := by simp [hn]
    rw [hd, if_neg hn, one_mul]
  have hfun : (fun (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) =>
      stBot κ A c0 pstar A (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)) =
      fun κd τ => clLocalSummand A.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base
        ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := funext fun κd => funext fun τ => hint κd τ
  refine ⟨?_, ?_⟩
  · unfold twistedLocalKernelM clLocalKernelModC
    show (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) * _ = _
    congr 1
    refine tsum_congr fun κd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    beta_reduce
    rw [hint κd τ]
  · refine BOKd.congr (BOKd.lowMod (BOKd_of_inputs c0.block (botR A c0) A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A)
      (stateLayer_isLayering A) κ.base hL (HF_of_all _ _ _ _ _ _ hF) ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2]) lam ![κ.t0, κ.t1, κ.t2]) ?_
    funext κd τ
    beta_reduce
    rw [hint κd τ]


end WaveTurbulence.VineEstS5C.FlatMod
