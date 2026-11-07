/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot10

/-! # V5 Step 4d-B2: the bottom vine, part 11 (the A-chart integrand of a state of the class; the skipped state)

For the chain region `c0` of the state `A` whose bottom joint is the lower joint of the member `pstar`, `botKernel` is the integrand of the chart
of `A` with the exceptional rows of a state `G` (`rowVal`, sign `ν`, clock/label pattern `tw`) and the `b`-factor of `A`; there is no
lower factor.  `stBot G` is the signed integrand of the state `G` (`ε_G = -1` iff `G` is twisted at `pstar`).
`botState_skip`: the skipped state `A` itself.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The region data of the chain region of `A`. -/
@[expose, reducible] noncomputable def botR (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) :
    CLRegionData A.skeleton c0.U c0.a c0.b := clRegionData A.skeleton c0.block c0.cl

/-- The A-chart integrand of a state with exceptional rows `(rq, rt)`, sign `ν`, clock/label pattern `tw`, without a lower factor. -/
@[expose] noncomputable def botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (x : GNode A.skeleton.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base c0.U c0.a c0.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u *
    (rowVal ν rq rt (u c0.b)
        (if tw then u (qrOf (A.family.placement pstar)) else u (qbOf (A.family.placement pstar)))
        (if tw then u (qbOf (A.family.placement pstar)) else u (qrOf (A.family.placement pstar)))
        (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode)
          else κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode))
        (if tw then κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)
          else κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode)) *
      bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u)

open Classical in
/-- The signed A-chart integrand of the state `G` (sign `-1` iff `G` is twisted at `pstar`). -/
@[expose] noncomputable def stBot (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (pstar : ι) (G : FamilyReconstruction w ι) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  epsOf A pstar G * botKernel κ A c0 pstar (decide (twAt A G pstar)) (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u

/-- The per-state conclusion: the kernel of the state at its chain region is `c ζ ∑' ∫ stBot` in the chart of `A`, with `BOKd`. -/
@[expose] def BotGoal (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (z : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) : Prop :=
  twistedLocalKernel z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h], ∫ τ : CLInternalTime (botR A c0),
          stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
            (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) ∧
    BOKd (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h] fun κd τ =>
      stBot κ A c0 pstar z.1 (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)

variable {pstar : ι}

/-- Same-chart states (skip, FALSE choice): `sameIntB` is `botKernel` with the pattern `tw = false`. -/
theorem sameIntB_eq_botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (G : FamilyReconstruction w ι)
    (D2 : ReconstructionData A.skeleton) (layer2 : GNode (D2.forest A.plain) → ℕ)
    (hLayer2 : IsLayering (D2.garden A.plain) layer2)
    (hσ : sigStar G pstar = (A.skeleton.sign (A.family.placement pstar).lower.toNode,
      nativeCoupleLayered D2 A.plain layer2 hLayer2 (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained),
      nativeChainLayered D2 A.plain layer2 hLayer2 (A.family.placement pstar).lower))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (hpx : PairedAt (A.family.placement pstar) x) (t : Fin 3 → ℝ)
    (u : GBranch A.skeleton.tree → ℝ) :
    sameIntB A.plain A.data D2 κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) layer2 hLayer2 κ.base
        (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) t x u =
      botKernel κ A c0 pstar false (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u := by
  have hex := exc_same (A.family.placement pstar) A.plain D2 κ.L κ.γ κ.δ κ.F layer2 hLayer2 κ.base
    (S := c0.U) (a := c0.a) hb0 x hpx u
  unfold sameIntB botKernel
  rw [hex]
  unfold nuOf rowQ rowT
  rw [hσ]
  simp only [Bool.false_eq_true, if_false]
  have e1 : A.skeleton.sign c0.b.toNode = A.skeleton.sign (A.family.placement pstar).lower.toNode := by rw [hb0]
  have e2 : nativeChainLayered D2 A.plain layer2 hLayer2 c0.b =
      nativeChainLayered D2 A.plain layer2 hLayer2 (A.family.placement pstar).lower := by rw [hb0]
  have e3 : x c0.b.toNode = x (A.family.placement pstar).lower.toNode := by rw [hb0]
  rw [e1, e2, e3]

open Classical in
theorem botState_skip (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoal κ A c0 pstar ⟨A, c0⟩ := by
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
      hS.b_mem_erase hS.p0_mem (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [sameIntB_eq_botKernel κ A c0 hb0 A A.data (stateLayer A) (stateLayer_isLayering A) rfl _ hpx]
    unfold stBot epsOf
    have hd : decide (twAt A A pstar) = false := by simp [hn]
    rw [hd, if_neg hn, one_mul]
  have hfun : (fun (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) =>
      stBot κ A c0 pstar A (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)) =
      fun κd τ => clLocalSummand A.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base
        ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := funext fun κd => funext fun τ => hint κd τ
  refine ⟨?_, ?_⟩
  · unfold twistedLocalKernel clLocalKernel
    show (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) * _ = _
    congr 1
    refine tsum_congr fun κd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact (hint κd τ).symm
  · refine BOKd.congr ?_ hfun.symm
    exact BOKd_of_inputs c0.block (botR A c0) A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
      κ.base hL (HF_of_all _ _ _ _ _ _ hF) _ _

end WaveTurbulence.VineEstS5B2
