/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSb1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt4

/-! # `SAbs` of the bundle kernel of a skipped state and of a FALSE-choice output (V5 Step 4d part C, `hAbs`, leaf `sb`)

For these states the bundle kernel is the native S-part `spart` of the state (same chart), so `sAbs_spart` applies. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ}

/-- Same-parameter variant of `κ` with the exterior times and upper boundary replaced. -/
def kparWithExt (κ : KPar d) (t : Fin 3 → ℝ) (e f : Mom d) : KPar d :=
  { κ with t0 := t 0, t1 := t 1, t2 := t 2, e := e, f := f }

theorem vec3_eta (t : Fin 3 → ℝ) : t = ![t 0, t 1, t 2] := by
  ext i; fin_cases i <;> rfl

theorem bundleKernel_skip_eq (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    bundleKernel κ A sp false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x.1
        (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) =
      spart A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.U sp.sb.a sp.sb.b x.1
        (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) := by
  have hS := SplitAt.slow sp
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (A.family.placement pstar).child.symm
  have h1 := bundleInt_eq_kernel κ A sp (fun _ _ _ => (1 : ℂ)) false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x σ
  have h2 : bundleInt κ A sp (fun _ _ _ => (1 : ℂ)) false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x σ =
      sInt sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
        sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) (fun _ _ _ => (1 : ℂ)) x σ := by
    rw [sInt_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
      (stateLayer_isLayering A) κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS
      κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) (fun _ _ _ => (1 : ℂ)) hS.b_mem_erase hS.p0_mem
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _) x σ]
    have hex := exc_same (A.family.placement pstar) A.plain A.data κ.L κ.γ κ.δ κ.F (stateLayer A)
      (stateLayer_isLayering A) κ.base (S := sp.sb.U) (a := sp.sb.a) hS.lower x.1 (hS.pairedAt_ext x)
      (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ)
    have hT : VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A) sp.sb.b =
        VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A)
          (A.family.placement pstar).lower := by
      rw [hS.lower]
    unfold sameInt bundleInt
    rw [hex, hn0, hn1, hT]
    rfl
  rw [h2] at h1
  unfold sInt at h1
  simpa using h1.symm


/-- **`SAbs` of the bundle kernel of the skipped state.** -/
theorem sAbs_bundle_skip (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    SAbs sp.RS κ.L κ.base (fun x u => bundleKernel κ A sp false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x u)
      (baseConst A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.RS) := by
  have hHF := HF_of_all A.data A.plain κ.L κ.F (stateLayer A) κ.base hF
  have key := sAbs_spart (hLayer := stateLayer_isLayering A) (γ := κ.γ) (δ := κ.δ) sp.sb.block sp.RS hHF hL
  refine (sAbs_congr_clock sp.RS κ.L κ.base _ _ _ ?_).mpr key
  intro t e f x σ
  have ht : clLocalClock sp.RS t σ = clLocalClock sp.RS ![t 0, t 1, t 2] σ := by rw [← vec3_eta t]
  rw [ht]
  exact bundleKernel_skip_eq (kparWithExt κ t e f) A sp x σ

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {kind : Bool}
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

theorem bundleKernel_false_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) false)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    bundleKernel κ A sp false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x.1
        (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) =
      spart con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base sp.sb.U sp.sb.a sp.sb.b x.1
        (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) := by
  have hS := SplitAt.slow sp
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (A.family.placement pstar).child.symm
  have h1 := bundleInt_eq_kernel κ A sp (fun _ _ _ => (1 : ℂ)) false
    (nuOf (opOut A pstar hcan hel htc hcc con) pstar) (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar)
    (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ
  have h2 : bundleInt κ A sp (fun _ _ _ => (1 : ℂ)) false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ =
      sInt sp.RS con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
        sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) (fun _ _ _ => (1 : ℂ)) x σ := by
    rw [← sameInt_false_eq κ A sp hcan hel htc hcc con (fun _ _ _ => (1 : ℂ)) x σ]
    refine (sInt_same A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS κ.t0 κ.t1 κ.t2 κ.e κ.f
      sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) (fun _ _ _ => (1 : ℂ)) hS.b_mem_erase hS.p0_mem ?_ ?_ ?_
      (VineEst.selDataEq_LF_false con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) _ _ (fun q hq => (Finset.mem_erase.mp hq).1)
        (fun v hv => hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm x σ).symm
    · intro q hq
      obtain ⟨hq0, _⟩ := Finset.mem_erase.mp hq
      have := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq0
      have hp : (A.source pstar hcan hel htc hcc).pairs false q = q := pairOfLeaf_firstLeaf A.skeleton A.plain q
      rw [hp] at this
      exact this.symm
    · intro v hv
      exact (native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
    · intro v _
      exact (coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v).symm
  rw [h2] at h1
  unfold sInt at h1
  simp only [mul_one] at h1
  exact h1.symm

/-- **`SAbs` of the bundle kernel of a FALSE-choice output.** -/
theorem sAbs_bundle_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false)
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    SAbs sp.RS κ.L κ.base (fun x u => bundleKernel κ A sp false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x u)
      (baseConst con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base sp.RS) := by
  have hHF := HF_of_all con.data A.plain κ.L κ.F (stateLayer (opOut A pstar hcan hel htc hcc con)) κ.base hF
  have key := sAbs_spart (hLayer := stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (γ := κ.γ) (δ := κ.δ)
    sp.sb.block sp.RS hHF hL
  refine (sAbs_congr_clock sp.RS κ.L κ.base _ _ _ ?_).mpr key
  intro t e f x σ
  have ht : clLocalClock sp.RS t σ = clLocalClock sp.RS ![t 0, t 1, t 2] σ := by rw [← vec3_eta t]
  rw [ht]
  exact bundleKernel_false_eq (kparWithExt κ t e f) A sp hcan hel htc hcc con x σ

end Ops

end WaveTurbulence.VineEstS5C
