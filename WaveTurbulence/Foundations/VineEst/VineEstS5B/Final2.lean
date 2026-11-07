/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final1

/-! # V5 Step 4d-B: the common lower factor `K̃` of `A` and `SOKAt` of `K̃^G` at the states of `Zp(A)` -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The common lower factor `K̃_T` at the state `A`. -/
@[expose] noncomputable def Ktil (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) : ℝ → Mom d → Mom d → ℂ :=
  ktilde (p := p) (kind := kind) κ A sp0 hA ⟨A, sp0⟩

open Classical in
theorem ktilde_eq (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) :
    ktilde (p := p) (kind := kind) κ A sp0 hA G = fun t E F' =>
      if twAt A G.1 pstar then Ktil (p := p) (kind := kind) κ A sp0 hA t F' E else Ktil (p := p) (kind := kind) κ A sp0 hA t E F' := by
  classical
  funext t E F'
  have hnA : ¬ twAt A A pstar := not_twAt_of_eq rfl
  simp only [Ktil, ktilde, kTor]
  by_cases htw : twAt A G.1 pstar
  · simp only [htw, hnA, if_true, if_false]
  · simp only [htw, hnA, if_false]

theorem ktilde_sum (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    ktilde (p := p) (kind := kind) κ A sp0 hA G = fun t E F' => ∑ x ∈ yFinset p kind pstar J A sp0 hA G, kT κ x.1 x.2 t E F' := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  funext t E F'
  unfold ktilde
  refine (sum_yG_eq_yA hc hA hG (fun x => kT κ x.1 x.2 t E F') (fun y => kTor κ A G.1 pstar y t E F') ?_).symm
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kT_rel κ hA hr hM hMy hxr hyr hxy t E F'

theorem sok_ktilde (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    SOKAt κ G.1 G.2 (ktilde (p := p) (kind := kind) κ A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kT κ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kT κ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF))
  rw [ktilde_sum κ A sp0 hA hG]
  exact sok_sum G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1) (stateLayer_isLayering G.1) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept) (yFinset p kind pstar J A sp0 hA G)
    (fun x t E F' => kT κ x.1 x.2 t E F') hsok

end WaveTurbulence.VineEstS5B
