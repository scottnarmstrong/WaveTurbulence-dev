/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.EpsPhase
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PiCurryVolume
public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.ClockDomains
import Mathlib.Tactic

/-!
# VINE-B: splitting the branch times of the skeleton

`timeSplit`: the measure-preserving equivalence `(𝒩(G_sk) → ℝ) ≃ᵐ (𝒩(G_sb) → ℝ) × Π_j CLInternalTime (U_j)`
induced by `branchSplit` (TARGET L1954–L1957: the times of the interior branches of `U_j` are integrated inside
`K^{U_j}`).  `glueTime` is its inverse in explicit form, and `extTime` reads a skeleton time vector off the `G_sb` times
(zero on unit interiors), from which the exterior clocks `(t_{u1}, t_{u21}, t_{u22})` of a unit are V5's
`clExternalTimes`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The time split. -/
noncomputable def timeSplit (hd : Disj blk) :
    (GBranch S.tree → ℝ) ≃ᵐ (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Φ.branchSplit hd).symm).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piCurry (fun (j : J) (_ : ↥(inter blk j)) => ℝ))))

theorem measurePreserving_timeSplit (hd : Disj blk) :
    MeasurePreserving (Φ.timeSplit hd) volume
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have h₁ := (measurePreserving_piCongrLeft (fun _ : GBranch S.tree => (volume : Measure ℝ))
    (Φ.branchSplit hd).symm).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : GBranch Gsb.tree ⊕ (Σ j, ↥(inter blk j)) => (volume : Measure ℝ))
  have h₃ : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (GBranch Gsb.tree → ℝ))
      (MeasurableEquiv.piCurry (fun (j : J) (_ : ↥(inter blk j)) => ℝ)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod (volume : Measure ((Σ j, ↥(inter blk j)) → ℝ)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (MeasurePreserving.id volume).prod (measurePreserving_piCurry_real (fun j : J => ↥(inter blk j)))
  exact h₃.comp (h₂.comp h₁)

/-- The glued skeleton times. -/
noncomputable def glueTime (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (v : GBranch S.tree) : ℝ :=
  match Φ.branchSplit hd v with
  | .inl c => τ' c
  | .inr x => τs x.1 x.2

theorem branchSplit_br (hd : Disj blk) (c : GBranch Gsb.tree) : Φ.branchSplit hd (Φ.br c) = .inl c := by
  unfold branchSplit
  exact (Equiv.ofBijective _ (Φ.assemble_bijective hd)).symm_apply_apply (.inl c)

theorem branchSplit_inter (hd : Disj blk) (j : J) (x : ↥(inter blk j)) :
    Φ.branchSplit hd x.1 = .inr ⟨j, x⟩ := by
  unfold branchSplit
  exact (Equiv.ofBijective _ (Φ.assemble_bijective hd)).symm_apply_apply (.inr ⟨j, x⟩)

theorem glueTime_br (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (c : GBranch Gsb.tree) : Φ.glueTime hd τ' τs (Φ.br c) = τ' c := by
  unfold glueTime; rw [Φ.branchSplit_br hd c]

theorem glueTime_inter (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (j : J) (x : ↥(inter blk j)) : Φ.glueTime hd τ' τs x.1 = τs j x := by
  unfold glueTime; rw [Φ.branchSplit_inter hd j x]

theorem timeSplit_glueTime (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) : Φ.timeSplit hd (Φ.glueTime hd τ' τs) = (τ', τs) := by
  refine Prod.ext ?_ ?_
  · funext c
    exact Φ.glueTime_br hd τ' τs c
  · funext j x
    exact Φ.glueTime_inter hd τ' τs j x

theorem timeSplit_symm (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    (Φ.timeSplit hd).symm (τ', τs) = Φ.glueTime hd τ' τs := by
  rw [← Φ.timeSplit_glueTime hd τ' τs, MeasurableEquiv.symm_apply_apply]

/-- The skeleton time vector read off the `G_sb` times (zero on unit interiors). -/
noncomputable def extTime (τ' : GBranch Gsb.tree → ℝ) (v : GBranch S.tree) : ℝ := by
  classical
  exact if h : Ret blk v.toNode then τ' (Φ.brEquiv.symm ⟨v, h⟩) else 0

theorem extTime_br (τ' : GBranch Gsb.tree → ℝ) (c : GBranch Gsb.tree) : Φ.extTime τ' (Φ.br c) = τ' c := by
  classical
  unfold extTime
  rw [dif_pos (Φ.ret_br c)]
  congr 1
  apply Φ.brEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem glueTime_ret (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    {v : GBranch S.tree} (hv : Ret blk v.toNode) : Φ.glueTime hd τ' τs v = Φ.extTime τ' v := by
  obtain ⟨c, rfl⟩ := Φ.exists_br hv
  rw [Φ.glueTime_br, Φ.extTime_br]

/-- The exterior clocks `(t_{u1}, t_{u21}, t_{u22})` of unit `j` (a leaf boundary child gets the dummy `0`). -/
noncomputable def clocks (τ' : GBranch Gsb.tree → ℝ) (j : J) : Fin 3 → ℝ :=
  clExternalTimes (regionOf (blk j)) (Φ.extTime τ')

theorem clocks_zero (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (j : J) :
    Φ.clocks τ' j 0 = τ' (Φ.hinge hd j) := by
  show Φ.extTime τ' (blk j).upper = _
  rw [← Φ.br_hinge hd j, Φ.extTime_br]

/-- On the atoms of unit `j`, V5's local clock at the exterior clocks is the glued time. -/
theorem clLocalClock_glue (hd : Disj blk) (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (j : J) {v : GBranch S.tree} (hv : v ∈ (blk j).atoms) :
    clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j) v = Φ.glueTime hd τ' τs v := by
  by_cases ha : v = (blk j).upper
  · subst ha
    rw [clLocalClock_upper, Φ.glueTime_ret hd τ' τs (ret_upper hd j)]
    rfl
  · have hm : v ∈ inter blk j := mem_inter.mpr ⟨hv, ha⟩
    rw [clLocalClock_internal _ _ _ ⟨v, hm⟩]
    exact (Φ.glueTime_inter hd τ' τs j ⟨v, hm⟩).symm

end SpliceShape

end WaveTurbulence.VineB
