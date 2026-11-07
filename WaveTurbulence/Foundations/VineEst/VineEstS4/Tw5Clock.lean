/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw4DecEq
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalTimes

/-! # K^T twist invariance, clocks and time domain (V5 Step 4b, step 3, part 5) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)

theorem mem_interior_iff (v : GBranch G.tree) :
    eB P v ∈ clInteriorBranches R' ↔ v ∈ clInteriorBranches R := by
  unfold clInteriorBranches
  rw [Finset.mem_erase, Finset.mem_erase, (eB P).injective.ne_iff]
  exact and_congr Iff.rfl (mem_twistedAtoms G P T v)

/-- The interior branches of the two regions correspond. -/
@[expose] noncomputable def iB : ↥(clInteriorBranches R) ≃ ↥(clInteriorBranches R') :=
  Equiv.subtypeEquiv (eB P) (fun v => (mem_interior_iff P R R' v).symm)

/-- The measurable, volume preserving identification of the internal times. -/
@[expose] noncomputable def tEquiv : CLInternalTime R ≃ᵐ CLInternalTime R' :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (iB P R R')

theorem tEquiv_measurePreserving :
    MeasurePreserving (tEquiv P R R') volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : ↥(clInteriorBranches R') => ℝ) (iB P R R')

theorem tEquiv_apply (τ : CLInternalTime R) (v : ↥(clInteriorBranches R)) :
    tEquiv P R R' τ (iB P R R' v) = τ v := by
  unfold tEquiv
  exact Equiv.piCongrLeft_apply_apply (fun _ : ↥(clInteriorBranches R') => ℝ) (iB P R R') τ v

omit hB hCL in
theorem clock_corr (t : Fin 3 → ℝ) (τ : CLInternalTime R) {v : GBranch G.tree} (hv : v ∈ T) :
    clLocalClock R' t (tEquiv P R R' τ) (eB P v) = clLocalClock R t τ v := by
  by_cases hl : v = P.lower
  · subst hl
    exact (clLocalClock_upper R' t _).trans (clLocalClock_upper R t τ).symm
  · have h1 : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hl, hv⟩
    have h2 := clLocalClock_internal R t τ ⟨v, h1⟩
    have h3 := clLocalClock_internal R' t (tEquiv P R R' τ) (iB P R R' ⟨v, h1⟩)
    exact h3.trans ((tEquiv_apply P R R' τ ⟨v, h1⟩).trans h2.symm)

include hB hCL R in
theorem parentClock_corr (t0 : ℝ) (u : GBranch G.tree → ℝ) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (hu : ∀ v ∈ T, u' (eB P v) = u v) {x : GNode G.tree} (hx : x ∈ clRealizationNodes G T)
    (hne : x ≠ P.lower.toNode) :
    parentClock t0 u' (naiveNodeEquiv G P x) = parentClock t0 u x := by
  obtain ⟨v, i, hxv, hv⟩ : ∃ (v : GBranch G.tree) (i : Fin 3), x = v.child i ∧ v ∈ T := by
    obtain ⟨hn, hp⟩ := cl_realization_parent hB R x hx hne
    exact ⟨x.parent hn, x.1.2.getLast hn, (Mole.parent_child_eq_node x hn).symm, hp⟩
  subst hxv
  rw [parentClock_child]
  by_cases hl : v = P.lower
  · subst hl
    have h1 := lower_naive_child G P i
    have h2 : parentClock t0 u' (naiveNodeEquiv G P (P.lower.child i)) = u' (eB P P.lower) := by
      rw [h1]; exact parentClock_child t0 u' (eB P P.lower) _
    exact h2.trans (hu _ hv)
  · have h1 := child_naive P hB hCL hv hl i
    have h2 : parentClock t0 u' (naiveNodeEquiv G P (v.child i)) = u' (eB P v) := by
      rw [h1]; exact parentClock_child t0 u' (eB P v) _
    exact h2.trans (hu _ hv)

theorem branching_naive (n : GNode G.tree) :
    n.1.2 ∈ (G.tree n.1.1).branching ↔
      (naiveNodeEquiv G P n).1.2 ∈ ((unitTwistGarden G P).tree (naiveNodeEquiv G P n).1.1).branching := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change b.toNode.1.2 ∈ (G.tree b.toNode.1.1).branching ↔
      (naiveNodeEquiv G P b.toNode).1.2 ∈ ((unitTwistGarden G P).tree (naiveNodeEquiv G P b.toNode).1.1).branching
    have hv : (naiveNodeEquiv G P b.toNode).1 = (eB P b).toNode.1 := congrArg Subtype.val (naiveNodeEquiv_branch G P b)
    rw [hv]
    exact iff_of_true b.2 (eB P b).2
  | inr l =>
    change l.toNode.1.2 ∈ (G.tree l.toNode.1.1).branching ↔
      (naiveNodeEquiv G P l.toNode).1.2 ∈ ((unitTwistGarden G P).tree (naiveNodeEquiv G P l.toNode).1.1).branching
    have hv : (naiveNodeEquiv G P l.toNode).1 = (eL P l).toNode.1 := congrArg Subtype.val (naiveNodeEquiv_leaf G P l)
    rw [hv]
    refine iff_of_false (fun h => Mole.branch_toNode_ne_leaf ⟨_, h⟩ l rfl) ?_
    exact fun h => Mole.branch_toNode_ne_leaf ⟨_, h⟩ (eL P l) rfl

include hB hCL in
theorem twDomain_iff (ℓ : GBranch G.tree → ℕ) (ℓ' : GBranch (unitTwistGarden G P).tree → ℕ)
    (hℓ : ∀ v ∈ T, ℓ' (eB P v) = ℓ v) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    tEquiv P R R' τ ∈ clLocalTimeDomain R' ℓ' t ↔ τ ∈ clLocalTimeDomain R ℓ t := by
  obtain ⟨he, hk, hp, hn⟩ := region_eq P hB hCL R R'
  have hzT : z ∈ T := hB.2.2.1
  have hzl : z ≠ P.lower := by
    intro h
    have := (Mole.cl_parent_strict_descendant G hB hCL).2
    rw [h] at this
    exact lt_irrefl _ this
  have hclock := fun v (hv : v ∈ T) => clock_corr P R R' t τ hv
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro H v
      have hv := H (iB P R R' v)
      have e1 : ℓ' (iB P R R' v).1 = ℓ v.1 := hℓ v.1 (Finset.mem_of_mem_erase v.2)
      have e2 : tEquiv P R R' τ (iB P R R' v) = τ v := tEquiv_apply P R R' τ v
      have e3 : parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)) (iB P R R' v).1.toNode =
          parentClock (t 0) (clLocalClock R t τ) v.1.toNode := by
        have hvT := Finset.mem_of_mem_erase v.2
        have hvl : v.1.toNode ≠ P.lower.toNode := fun h => (Finset.mem_erase.mp v.2).1 (Mole.branch_toNode_injective h)
        have := parentClock_corr P hB hCL R (t 0) (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ))
          (fun v hv => hclock v hv) ((branch_mem_clRealizationNodes v.1).mpr hvT) hvl
        exact (congrArg (parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)))
          (naiveNodeEquiv_branch G P v.1).symm).trans this
      rw [e1, e2, e3] at hv
      exact hv
    · intro H v'
      obtain ⟨v, rfl⟩ := (iB P R R').surjective v'
      have hv := H v
      have e1 : ℓ' (iB P R R' v).1 = ℓ v.1 := hℓ v.1 (Finset.mem_of_mem_erase v.2)
      have e2 : tEquiv P R R' τ (iB P R R' v) = τ v := tEquiv_apply P R R' τ v
      have e3 : parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)) (iB P R R' v).1.toNode =
          parentClock (t 0) (clLocalClock R t τ) v.1.toNode := by
        have hvT := Finset.mem_of_mem_erase v.2
        have hvl : v.1.toNode ≠ P.lower.toNode := fun h => (Finset.mem_erase.mp v.2).1 (Mole.branch_toNode_injective h)
        have := parentClock_corr P hB hCL R (t 0) (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ))
          (fun v hv => hclock v hv) ((branch_mem_clRealizationNodes v.1).mpr hvT) hvl
        exact (congrArg (parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)))
          (naiveNodeEquiv_branch G P v.1).symm).trans this
      rw [e1, e2, e3]
      exact hv
  · have hc := child_naive P hB hCL hzT hzl R.positive
    have hb := branching_naive P (z.child R.positive)
    have hv : (naiveNodeEquiv G P (z.child R.positive)).1 = ((eB P z).child R.positive).1 := congrArg Subtype.val hc
    rw [hv] at hb
    have hcl := hclock z hzT
    rw [hp]
    constructor
    · intro H hA
      have := H (hb.mp hA)
      rwa [hcl] at this
    · intro H hA
      have := H (hb.mpr hA)
      rwa [← hcl] at this
  · have hc := child_naive P hB hCL hzT hzl R.negative
    have hb := branching_naive P (z.child R.negative)
    have hv : (naiveNodeEquiv G P (z.child R.negative)).1 = ((eB P z).child R.negative).1 := congrArg Subtype.val hc
    rw [hv] at hb
    have hcl := hclock z hzT
    rw [hn]
    constructor
    · intro H hA
      have := H (hb.mp hA)
      rwa [hcl] at this
    · intro H hA
      have := H (hb.mpr hA)
      rwa [← hcl] at this

end WaveTurbulence.VineEstS4
