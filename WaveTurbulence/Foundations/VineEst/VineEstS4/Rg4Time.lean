/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg3Fac
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw5Clock

/-! # Rigid relocation of the upper block: clocks and the factors `n₁`, `ζ` (V5 Step 4b, step 4, WP-B part 4) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
  MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (RS : CLRegionData G S a b)
  (RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b))

theorem mem_interior_rigid (v : GBranch G.tree) :
    eB P v ∈ clInteriorBranches RS' ↔ v ∈ clInteriorBranches RS :=
  mem_erase_twisted P (b := a) v

/-- The interior branches of the two regions of the upper block correspond. -/
@[expose] noncomputable def iBS : ↥(clInteriorBranches RS) ≃ ↥(clInteriorBranches RS') :=
  Equiv.subtypeEquiv (eB P) (fun v => (mem_interior_rigid P RS RS' v).symm)

/-- The measurable, volume preserving identification of the internal times of the upper block. -/
@[expose] noncomputable def tEquivS : CLInternalTime RS ≃ᵐ CLInternalTime RS' :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (iBS P RS RS')

theorem tEquivS_measurePreserving : MeasurePreserving (tEquivS P RS RS') volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : ↥(clInteriorBranches RS') => ℝ) (iBS P RS RS')

theorem tEquivS_apply (τ : CLInternalTime RS) (v : ↥(clInteriorBranches RS)) :
    tEquivS P RS RS' τ (iBS P RS RS' v) = τ v := by
  unfold tEquivS
  exact Equiv.piCongrLeft_apply_apply (fun _ : ↥(clInteriorBranches RS') => ℝ) (iBS P RS RS') τ v

theorem clockS_corr (t : Fin 3 → ℝ) (τ : CLInternalTime RS) {v : GBranch G.tree} (hv : v ∈ S) :
    clLocalClock RS' t (tEquivS P RS RS' τ) (eB P v) = clLocalClock RS t τ v := by
  by_cases hl : v = a
  · subst hl
    exact (clLocalClock_upper RS' t _).trans (clLocalClock_upper RS t τ).symm
  · have h1 : v ∈ clInteriorBranches RS := Finset.mem_erase.mpr ⟨hl, hv⟩
    have h2 := clLocalClock_internal RS t τ ⟨v, h1⟩
    have h3 := clLocalClock_internal RS' t (tEquivS P RS RS' τ) (iBS P RS RS' ⟨v, h1⟩)
    exact h3.trans ((tEquivS_apply P RS RS' τ ⟨v, h1⟩).trans h2.symm)

theorem order1_rigid : clLocalOrder1 RS' = clLocalOrder1 RS := by
  unfold clLocalOrder1
  exact (Finset.card_equiv (eB P) (fun v => (mem_interior_rigid P RS RS' v).symm)).symm

theorem zeta_rigid (hR : RigidAt P S b) : clLocalZeta RS' = clLocalZeta RS := by
  unfold clLocalZeta
  refine (Finset.prod_equiv (eB P) (fun v => (mem_interior_rigid P RS RS' v).symm) (fun v hv => ?_)).symm
  have hvl : v ≠ P.lower := hR.ne_lower (Finset.mem_of_mem_erase hv)
  have hs : (unitTwistGarden G P).sign (eB P v).toNode = G.sign v.toNode := by
    rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, coreBranchEquiv_sign, ite_eq_right hvl]
  rw [hs]

end WaveTurbulence.VineEstS4
