/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp15SokOp
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp10KT

/-! # (tildeJ2) for an abstract split (V5 Step 4b, step 4)

`tildeJ2_of_split`: for a start state `A` with a prime skeleton and a split `sp0` (with the members that may carry an operation
below `pstar` in `J`, all other members except `pstar` carrying no operation at `A`),
`∑_{x ∈ canon} K^U_x = ∑_{G ∈ Zp(A)} sSumAt G (K̃_T^G)`, where `K̃_T^G(t; E, F') = ∑_{y ∈ Y(A)} K^{T_y}_y(t; E, F')` for `G` untwisted at
`pstar` and with `(E, F')` exchanged for a twist at `pstar` (the common factor of TARGET (tildeJ2)).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The common lower factor `K̃_T` for the twist `G` of `A` at `pstar`: the sum of the lower kernels over `Y(A)`. -/
@[expose] noncomputable def ktilde (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, kTor κ A G.1 pstar y t E F'

theorem SOKAt_kT (κ : KPar d) (X : FamilyReconstruction w ι) (sx : SplitAt X.skeleton X.family pstar J) (hL : κ.L ≠ 0)
    (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) : SOKAt κ X sx (kT κ X sx) := by
  have hex : sx.RT.excluded = sx.RS.kept := split_excluded_b sx.sb.block sx.hT sx.hi sx.hU sx.RS sx.RT
  have h := sok_KT sx.sb.block sx.hT sx.hi sx.hU sx.RU sx.RS sx.RT X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X)
    (stateLayer_isLayering X) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h hL hF
  have hb0 : clBoundaryNodes sx.RT 0 = sx.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sx.RT 1 = sx.sb.b.child sx.RS.kept := by
    change sx.sb.b.child sx.RT.excluded = _
    rw [hex]
  unfold SOKAt kT
  exact (SOK_nodes_congr sx.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f hb0.symm hb1.symm _).mpr h

theorem HF_of_all {w d : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (L : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (base : Mom d)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |F k (base + latticePoint L n)|) : HF D hG L F layer base :=
  fun _ _ => hF _

/-- **(tildeJ2) for an abstract split.** -/
theorem tildeJ2_of_split (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, kU κ x.1 x.2 =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA, sSumAt κ G.1 G.2 (ktilde (p := p) (kind := kind) κ A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  rw [sum_canon hc hA]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hr := (mem_zpFinset hA).mp hG
  have ha : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, kU κ x.1 x.2 = sSumAt κ G.1 G.2 (kT κ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    rw [kU_eq_sSumAt κ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF)]
    exact sSumAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _
  rw [Finset.sum_congr rfl ha]
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kT κ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kT κ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF))
  have hlin := sSum_finsetSum G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1) (stateLayer_isLayering G.1)
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept)
    (yFinset p kind pstar J A sp0 hA G) (fun x => kT κ x.1 x.2) hsok
  unfold sSumAt at hlin ⊢
  rw [← hlin]
  congr 1
  funext t E F'
  unfold ktilde
  refine sum_yG_eq_yA hc hA hG (fun x => kT κ x.1 x.2 t E F') (fun y => kTor κ A G.1 pstar y t E F') ?_
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kT_rel κ hA hr hM hMy hxr hyr hxy t E F'

end WaveTurbulence.VineEstS4
