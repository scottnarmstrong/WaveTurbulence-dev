/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Fubini2
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp19Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp15SokOp

/-! # FLAT-MOD (R60), (tildeJ2) for the modulated kernels

`twistedLocalKernelM` (the member term of `Cont.twistedRecenteredModC`), `kUM`, `kUM_eq_sSumAt` (the kernel of a split state is its
S-side with the lower factor `kTM`), `SOKAt_kTM`, `kTorM`, `ktildeM`, `kTM_rel` (the fibre kernel is the exchanged kernel of `y`),
`tildeJ2_of_splitM`, **`tildeJ2_canonM`**: `∑_{y ∈ canon} K^{U,λ}_y = ∑_{G ∈ Zp(A)} sSumAt G (K̃^{G,λ})`.  The combinatorics
(`sum_canon`, `sSumAt_reachBelow`, `SOKAt_reachBelow`, `sum_yG_eq_yA`) is the unmodulated one: it is generic in the lower factor.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- `K^{U,λ}_{(G')}` of a state at a transported region (member term of `Cont.twistedRecenteredModC`). -/
noncomputable def twistedLocalKernelM (lam : ℝ) {ι : Type*} (Bs : FamilyReconstruction w ι)
    (c : ChainAt Bs.skeleton Bs.family) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  clLocalKernelModC Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs) (stateLayer_isLayering Bs)
    base lam tUpper tPositive tNegative e f g h

theorem clLocalKernelModC_idx {G : Garden w} {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree}
    (hU : U = U') (ha : a = a') (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b')
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      clLocalKernelModC D hG R' L γ δ F layer hLayer base lam t0 t1 t2 e f g h := by
  subst hU ha hb
  rw [regionData_subsingleton R R']

section State
variable (κ : KPar d) (lam : ℝ) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)

/-- `K^{U,λ}` of the state at its chain region. -/
noncomputable def kUM : ℂ :=
  twistedLocalKernelM lam X sp.c κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h

theorem kUM_eq_sSumAt (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) :
    kUM κ lam X sp = sSumAt κ X sp (kTM κ lam X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have h1 := clLocalKernelModC_split_KT sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h hL hF
  unfold kUM twistedLocalKernelM
  rw [clLocalKernelModC_idx sp.union sp.sa.symm sp.tbb.symm (clRegionData X.skeleton sp.c.block sp.c.cl) sp.RU]
  rw [h1]
  unfold sSumAt kTM
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  rw [hb0, hb1]
  rfl

theorem SOKAt_kTM (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) :
    SOKAt κ X sp (kTM κ lam X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have h := sok_KTM sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X)
    (stateLayer_isLayering X) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h hL hF
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  unfold SOKAt kTM
  exact (SOK_nodes_congr sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f hb0.symm hb1.symm _).mpr h

end State

open Classical in
/-- The lower kernel of `y`, with the first two boundary momenta exchanged iff `G` is a twist at `pstar` (modulated). -/
noncomputable def kTorM (κ : KPar d) (lam : ℝ) (A G : FamilyReconstruction w ι) (pstar : ι) (y : ST w ι pstar J) :
    ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  if twAt A G pstar then kTM κ lam y.1 y.2 t F' E else kTM κ lam y.1 y.2 t E F'

/-- The common lower factor `K̃^λ_T` for the twist `G` of `A` at `pstar`. -/
noncomputable def ktildeM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, kTorM κ lam A G.1 pstar y t E F'

section Rel
variable (κ : KPar d) (lam : ℝ) {A : FamilyReconstruction w ι} {sp0 : SplitAt A.skeleton A.family pstar J}

/-- **The fibre kernel is the exchanged kernel of `y`** (modulated `kT_rel`). -/
theorem kTM_rel (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J}
    (hG : ReachSp p kind pstar J [pstar] A sp0 G.1 G.2) {x y : ST w ι pstar J}
    {M My : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) (hMy : My.Perm (Finset.univ.erase pstar).toList)
    (hx : ReachSp p kind pstar J M G.1 G.2 x.1 x.2) (hy : ReachSp p kind pstar J My A sp0 y.1 y.2)
    (hxy : FamilyBatch p kind [pstar] y.1 x.1) (t : ℝ) (E F' : Mom d) :
    kTM κ lam x.1 x.2 t E F' = kTorM κ lam A G.1 pstar y t E F' := by
  classical
  have hsy : sigStar y.1 pstar = sigStar A pstar := sigStar_batch hy.batch (not_mem_erase hMy)
  have hsx : sigStar x.1 pstar = sigStar G.1 pstar := sigStar_batch hx.batch (not_mem_erase hM)
  have hxA : ReachSp p kind pstar J ([pstar] ++ M) A sp0 x.1 x.2 := ReachSp.append hG hx
  obtain ⟨X, sx⟩ := x
  simp only at hxy hsx hxA ⊢
  cases hxy with
  | skip _ h1 =>
    cases h1
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0 y.1 y.2 := ReachSp.append hy (ReachSp.skips y.2 _)
    have e : sx = y.2 := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hn : ¬ twAt A G.1 pstar := not_twAt_of_eq (hsx.symm.trans hsy)
    unfold kTorM
    rw [if_neg hn]
  | apply op h1 =>
    cases h1
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) y.1 pstar))
        (SplitAt.nextA y.1 y.2 pstar ε) := ReachSp.append hy (.apply _ (.nil _ _))
    have e : sx = SplitAt.nextA y.1 y.2 pstar ε := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hs := sigStar_output y.1 pstar hcan hel htc hcc con
    cases ε
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = (sigStar A pstar).1 := by
        rw [hs]
        exact h0
      have hn : ¬ twAt A G.1 pstar := fun hh => hh (hsx ▸ h1)
      unfold kTorM
      rw [if_neg hn]
      exact kTM_op_false κ lam y.1 y.2 hcan hel htc hcc con t E F'
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = -(sigStar A pstar).1 := by
        rw [hs]
        refine (sign_out_true y.1 pstar hcan hel htc hcc con).trans ?_
        exact congrArg (fun z => -z) h0
      have hn : twAt A G.1 pstar := by
        intro hh
        apply units_ne_neg (sigStar A pstar).1
        rw [← h1, hsx, hh]
      unfold kTorM
      rw [if_pos hn]
      exact kTM_op_true κ lam y.1 y.2 hcan hel htc hcc con t E F'

end Rel

/-- **(tildeJ2) for an abstract split, modulated.** -/
theorem tildeJ2_of_splitM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, kUM κ lam x.1 x.2 =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  rw [sum_canon hc hA]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hr := (mem_zpFinset hA).mp hG
  have ha : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, kUM κ lam x.1 x.2 = sSumAt κ G.1 G.2 (kTM κ lam x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    rw [kUM_eq_sSumAt κ lam x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF)]
    exact sSumAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _
  rw [Finset.sum_congr rfl ha]
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kTM κ lam x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kTM κ lam x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF))
  have hlin := sSum_finsetSum G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1) (stateLayer_isLayering G.1)
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept)
    (yFinset p kind pstar J A sp0 hA G) (fun x => kTM κ lam x.1 x.2) hsok
  unfold sSumAt at hlin ⊢
  rw [← hlin]
  congr 1
  funext t E F'
  unfold ktildeM
  refine sum_yG_eq_yA hc hA hG (fun x => kTM κ lam x.1 x.2 t E F') (fun y => kTorM κ lam A G.1 pstar y t E F') ?_
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kTM_rel κ lam hA hr hM hMy hxr hyr hxy t E F'

/-- **(tildeJ2) over the canonical representatives, modulated.** -/
theorem tildeJ2_canonM (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ y ∈ canonFinsetK p kind A sp0.c,
        twistedLocalKernelM lam y.1 y.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, sSumAt κ G.1 G.2 (ktildeM (p := p) (kind := kind) κ lam A sp0 hA G) := by
  rw [← sum_canonSp_eq_canon A sp0 hA
    (fun y => twistedLocalKernelM lam y.1 y.2 κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h)]
  exact tildeJ2_of_splitM κ lam A sp0 hA hA0 hL hF

end WaveTurbulence.VineEstS5C.FlatMod
