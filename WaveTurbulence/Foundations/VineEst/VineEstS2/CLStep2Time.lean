/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Weights
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots

/-! # TARGET Step 2: the time-window decomposition

The first joint clock `t₀¹` of the sumint shape is the clock of the lower joint `b`, and the
source clock domain is, up to the unit-interval boundaries, the sumint input time domain with
`q` the layers and the constraints the child/parent order. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assemblyPieceAt_zero_lower (B : CLChainAssembly G R n) (hI : 0 < n) :
    (assemblyPieceAt B ⟨0,hI⟩).lower = b := by
  cases B with
  | single hV _ => rfl
  | append B hT hi hU R => rfl

theorem assemblyClockAtom_first (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hI : 0 < (assemblyShape hM9 B).I) :
    (assemblyClockAtomEquiv hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := by
  have hI' : 0 < n := hI
  have h := assemblyAtomEquiv_input hM9 B ⟨0,hI'⟩ (assemblyChartAt hM9 B ⟨0,hI'⟩).indexing.shape.x0
  have hl := (assemblyChartAt hM9 B ⟨0,hI'⟩).indexing.lower
  have hs : assemblyTimeEquiv hM9 B (.inl ⟨⟨0,hI⟩,0⟩) =
      (assemblyInputEquiv hM9 B).symm ⟨⟨0,hI'⟩,(assemblyChartAt hM9 B ⟨0,hI'⟩).indexing.shape.x0⟩ := by
    unfold assemblyTimeEquiv
    rw [Equiv.trans_apply, Sumint.timeVectorEquiv_zero, Equiv.symm_apply_eq]
    unfold assemblyVectorEquiv
    have hq := (assemblyInputEquiv hM9 B).apply_symm_apply
      (⟨⟨0,hI'⟩,(assemblyChartAt hM9 B ⟨0,hI'⟩).indexing.shape.x0⟩ :
        Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n)
    refine Eq.trans ?_ (congrArg (Equiv.sigmaCongrRight
      (familySlotEquiv (fun i => (assemblyPieceAt B i).vineType) fun i =>
        (assemblyChartAt hM9 B i).indexing.shape)) hq).symm
    exact Sigma.ext rfl (heq_of_eq (familySlotEquiv_x0 _ _ _).symm)
  unfold assemblyClockAtomEquiv
  rw [Equiv.trans_apply, hs, h]
  exact hl.trans (assemblyPieceAt_zero_lower B hI')

theorem parentClock_interior (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (top : ℝ)
    (u : GBranch G.tree → ℝ) (v : GBranch G.tree) (hv : v ∈ U) (hva : v ≠ a) :
    ∃ hn : v.1.2 ≠ [], v.toNode.parent hn ∈ U ∧ parentClock top u v.toNode = u (v.toNode.parent hn) := by
  obtain ⟨hn, hp⟩ := cl_realization_parent hU R v.toNode ((branch_mem_clRealizationNodes v).mpr hv)
    (fun he => hva (Mole.branch_toNode_injective he))
  exact ⟨hn, hp, parentClock_nonroot top u v.toNode hn⟩

/-- Every interior clock lies below the top clock, by induction along the parent chain. -/
theorem interior_clock_lt_top (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (top : ℝ)
    (u : GBranch G.tree → ℝ) (hu : u a = top)
    (h : ∀ v ∈ U, v ≠ a → u v < parentClock top u v.toNode) :
    ∀ (m : ℕ) (v : GBranch G.tree), v.1.2.length = m → v ∈ U → v ≠ a → u v < top := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hm hv hva
    obtain ⟨hn, hp, he⟩ := parentClock_interior hU R top u v hv hva
    have h1 := h v hv hva
    rw [he] at h1
    by_cases hpa : v.toNode.parent hn = a
    · rw [hpa, hu] at h1
      exact h1
    · have hl : (v.toNode.parent hn).1.2.length < m := by
        rw [← hm]
        change v.1.2.dropLast.length < v.1.2.length
        have hp0 : v.1.2.length ≠ 0 := fun he0 => hn (List.length_eq_zero_iff.mp he0)
        rw [List.length_dropLast]
        omega
      exact h1.trans (ih _ hl _ rfl hp hpa)

/-- The unit-interval index of each sumint clock: the layer of its source branch. -/
noncomputable def assemblyTimeQ (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (layerB : GBranch G.tree → ℕ) : (assemblyShape hM9 B).TVar → ℕ :=
  fun s => layerB (assemblyClockAtomEquiv hM9 B s).1

open Classical in
/-- The order constraints `s < s'` of the sumint input time domain: `s'` is the parent branch of `s`. -/
noncomputable def assemblyTimeConstraints (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar) :=
  Finset.univ.filter fun c => ∃ hn : (assemblyClockAtomEquiv hM9 B c.1).1.1.2 ≠ [],
    (assemblyClockAtomEquiv hM9 B c.1).1.toNode.parent hn = (assemblyClockAtomEquiv hM9 B c.2).1

/-- The input time domain of `sumint` with the source layers and parent order. -/
def assemblyTimeDomain (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (layerB : GBranch G.tree → ℕ)
    (hI : 0 < (assemblyShape hM9 B).I) (t : Fin 3 → ℝ) : Set ((assemblyShape hM9 B).TVar → ℝ) :=
  {τ | (∀ s, (assemblyTimeQ hM9 B layerB s : ℝ) ≤ τ s ∧ τ s ≤ assemblyTimeQ hM9 B layerB s + 1 ∧
      τ s < t 0) ∧
    max (t 1) (t 2) < τ (.inl ⟨⟨0,hI⟩,0⟩) ∧ ∀ c ∈ assemblyTimeConstraints hM9 B, τ c.1 < τ c.2}

variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

theorem clLocalClock_slot (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (s : (assemblyShape hM9 B).TVar) :
    clLocalClock R t (assemblyClockEquiv hM9 B τ) (assemblyClockAtomEquiv hM9 B s).1 = τ s := by
  exact (assemblyClock_internal hM9 B t τ (assemblyClockAtomEquiv hM9 B s)).trans
    (congrArg τ (Equiv.symm_apply_apply _ _))

theorem assemblyClock_apply_slot (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (s : (assemblyShape hM9 B).TVar) :
    assemblyClockEquiv hM9 B τ (assemblyClockAtomEquiv hM9 B s) = τ s :=
  (clLocalClock_internal R t (assemblyClockEquiv hM9 B τ) _).symm.trans (clLocalClock_slot hM9 B t τ s)

/-- Parent clock of the branch of a slot: the top clock or another slot's clock, the latter
exactly when the pair is in the constraint set. -/
theorem slot_parent_clock (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (s : (assemblyShape hM9 B).TVar) :
    (parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ))
        (assemblyClockAtomEquiv hM9 B s).1.toNode = t 0 ∧
      ∃ hn : (assemblyClockAtomEquiv hM9 B s).1.1.2 ≠ [],
        (assemblyClockAtomEquiv hM9 B s).1.toNode.parent hn = a) ∨
    ∃ s', (s, s') ∈ assemblyTimeConstraints hM9 B ∧
      parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ))
        (assemblyClockAtomEquiv hM9 B s).1.toNode = τ s' := by
  classical
  have hs := (assemblyClockAtomEquiv hM9 B s).2
  have hs' := Finset.mem_erase.mp hs
  obtain ⟨hn, hp, he⟩ := parentClock_interior B.isBlock R (t 0)
    (clLocalClock R t (assemblyClockEquiv hM9 B τ)) _ hs'.2 hs'.1
  by_cases hpa : (assemblyClockAtomEquiv hM9 B s).1.toNode.parent hn = a
  · left
    refine ⟨?_, hn, hpa⟩
    rw [he, hpa]
    exact clLocalClock_upper R t _
  · right
    have hmem : (assemblyClockAtomEquiv hM9 B s).1.toNode.parent hn ∈ U.erase a :=
      Finset.mem_erase.mpr ⟨hpa, hp⟩
    refine ⟨(assemblyClockAtomEquiv hM9 B).symm ⟨_, hmem⟩, ?_, ?_⟩
    · unfold assemblyTimeConstraints
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hn, ?_⟩
      rw [Equiv.apply_symm_apply]
    · rw [he]
      have := clLocalClock_slot hM9 B t τ ((assemblyClockAtomEquiv hM9 B).symm ⟨_, hmem⟩)
      rw [Equiv.apply_symm_apply] at this
      exact this

theorem constraint_parent_clock (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (c : (assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)
    (hc : c ∈ assemblyTimeConstraints hM9 B) :
    parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ))
        (assemblyClockAtomEquiv hM9 B c.1).1.toNode = τ c.2 := by
  classical
  unfold assemblyTimeConstraints at hc
  obtain ⟨_, hn, hp⟩ := Finset.mem_filter.mp hc
  rw [parentClock_nonroot _ _ _ hn, hp]
  exact clLocalClock_slot hM9 B t τ c.2

/-- Conversely, off the unit-interval boundaries the sumint input time domain lies in the source
clock domain. -/
theorem source_of_assemblyTimeDomain (hI : 0 < (assemblyShape hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ)
    (hτ : τ ∈ assemblyTimeDomain hM9 B layerB hI t)
    (hbd : ∀ s, τ s ≠ assemblyTimeQ hM9 B layerB s ∧ τ s ≠ assemblyTimeQ hM9 B layerB s + 1) :
    assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R layerB t := by
  obtain ⟨hwin, hjoin, hcon⟩ := hτ
  have hb : (assemblyClockAtomEquiv hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := assemblyClockAtom_first hM9 B hI
  have hbclock : clLocalClock R t (assemblyClockEquiv hM9 B τ) b = τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have := clLocalClock_slot hM9 B t τ (.inl ⟨⟨0,hI⟩,0⟩)
    rwa [hb] at this
  refine ⟨fun v => ?_, fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨s, rfl⟩ := (assemblyClockAtomEquiv hM9 B).surjective v
    have hv : clLocalClock R t (assemblyClockEquiv hM9 B τ) (assemblyClockAtomEquiv hM9 B s).1 = τ s :=
      clLocalClock_slot hM9 B t τ s
    have e1 : (assemblyClockEquiv hM9 B τ) (assemblyClockAtomEquiv hM9 B s) = τ s :=
      assemblyClock_apply_slot hM9 B t τ s
    obtain ⟨h1, h2, h3⟩ := hwin s
    have hq0 : (0 : ℝ) ≤ assemblyTimeQ hM9 B layerB s := Nat.cast_nonneg _
    have hlow : (assemblyTimeQ hM9 B layerB s : ℝ) < τ s := lt_of_le_of_ne h1 (hbd s).1.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; exact hlow
    · rw [e1]; exact lt_of_le_of_ne h2 (hbd s).2
    · rw [e1]; exact hq0.trans_lt hlow
    · rw [e1]
      rcases slot_parent_clock hM9 B t τ s with ⟨hp, _⟩ | ⟨s', hs', hp⟩
      · rw [hp]; exact h3
      · rw [hp]; exact hcon _ hs'
  · rw [hbclock]
    exact (le_max_left _ _).trans_lt hjoin
  · rw [hbclock]
    exact (le_max_right _ _).trans_lt hjoin

theorem measurableSet_assemblyTimeDomain (hI : 0 < (assemblyShape hM9 B).I)
    (layerB : GBranch G.tree → ℕ) (t : Fin 3 → ℝ) :
    MeasurableSet (assemblyTimeDomain hM9 B layerB hI t) := by
  unfold assemblyTimeDomain
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun s => ?_) (MeasurableSet.inter ?_
    (MeasurableSet.iInter fun c => MeasurableSet.iInter fun hc => ?_))
  · refine MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop))
      (MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop))
        (measurableSet_lt (by fun_prop) (by fun_prop)))
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)

end WaveTurbulence.VineEstS2
