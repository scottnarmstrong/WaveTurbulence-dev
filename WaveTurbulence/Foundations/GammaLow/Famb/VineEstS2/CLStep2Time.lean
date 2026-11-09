/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Weights
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time` (sha256 53f62a14771403a5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # TARGET Step 2: the time-window decomposition

The first joint clock `t₀¹` of the sumint shape is the clock of the lower joint `b`, and the
source clock domain is, up to the unit-interval boundaries, the sumint input time domain with
`q` the layers and the constraints the child/parent order. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assemblyPieceAt_zero_lowerΓ (B : CLChainAssemblyΓ γF G R n) (hI : 0 < n) :
    (assemblyPieceAtΓ B ⟨0,hI⟩).lower = b := by
  cases B with
  | single hV _ => rfl
  | append B hT hi hU R => rfl

theorem assemblyClockAtom_firstΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (hI : 0 < (assemblyShapeΓ hM9 B).I) :
    (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := by
  have hI' : 0 < n := hI
  have h := assemblyAtomEquiv_inputΓ hM9 B ⟨0,hI'⟩ (assemblyChartAtΓ hM9 B ⟨0,hI'⟩).indexing.shape.x0
  have hl := (assemblyChartAtΓ hM9 B ⟨0,hI'⟩).indexing.lower
  have hs : assemblyTimeEquivΓ hM9 B (.inl ⟨⟨0,hI⟩,0⟩) =
      (assemblyInputEquivΓ hM9 B).symm ⟨⟨0,hI'⟩,(assemblyChartAtΓ hM9 B ⟨0,hI'⟩).indexing.shape.x0⟩ := by
    unfold assemblyTimeEquivΓ
    rw [Equiv.trans_apply, Sumint.timeVectorEquiv_zero, Equiv.symm_apply_eq]
    unfold assemblyVectorEquivΓ
    have hq := (assemblyInputEquivΓ hM9 B).apply_symm_apply
      (⟨⟨0,hI'⟩,(assemblyChartAtΓ hM9 B ⟨0,hI'⟩).indexing.shape.x0⟩ :
        Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n)
    refine Eq.trans ?_ (congrArg (Equiv.sigmaCongrRight
      (familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label) fun i =>
        (assemblyChartAtΓ hM9 B i).indexing.shape)) hq).symm
    exact Sigma.ext rfl (heq_of_eq (familySlotEquiv_x0 _ _ _).symm)
  unfold assemblyClockAtomEquivΓ
  rw [Equiv.trans_apply, hs, h]
  exact hl.trans (assemblyPieceAt_zero_lowerΓ B hI')

/-- The unit-interval index of each sumint clock: the layer of its source branch. -/
noncomputable def assemblyTimeQΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (layerB : GBranch G.tree → ℕ) : (assemblyShapeΓ hM9 B).TVar → ℕ :=
  fun s => layerB (assemblyClockAtomEquivΓ hM9 B s).1

open Classical in
/-- The order constraints `s < s'` of the sumint input time domain: `s'` is the parent branch of `s`. -/
noncomputable def assemblyTimeConstraintsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar) :=
  Finset.univ.filter fun c => ∃ hn : (assemblyClockAtomEquivΓ hM9 B c.1).1.1.2 ≠ [],
    (assemblyClockAtomEquivΓ hM9 B c.1).1.toNode.parent hn = (assemblyClockAtomEquivΓ hM9 B c.2).1

variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

theorem clLocalClock_slotΓ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (s : (assemblyShapeΓ hM9 B).TVar) :
    clLocalClock R t (assemblyClockEquivΓ hM9 B τ) (assemblyClockAtomEquivΓ hM9 B s).1 = τ s := by
  exact (assemblyClock_internalΓ hM9 B t τ (assemblyClockAtomEquivΓ hM9 B s)).trans
    (congrArg τ (Equiv.symm_apply_apply _ _))

/-- Parent clock of the branch of a slot: the top clock or another slot's clock, the latter
exactly when the pair is in the constraint set. -/
theorem slot_parent_clockΓ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (s : (assemblyShapeΓ hM9 B).TVar) :
    (parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ))
        (assemblyClockAtomEquivΓ hM9 B s).1.toNode = t 0 ∧
      ∃ hn : (assemblyClockAtomEquivΓ hM9 B s).1.1.2 ≠ [],
        (assemblyClockAtomEquivΓ hM9 B s).1.toNode.parent hn = a) ∨
    ∃ s', (s, s') ∈ assemblyTimeConstraintsΓ hM9 B ∧
      parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ))
        (assemblyClockAtomEquivΓ hM9 B s).1.toNode = τ s' := by
  classical
  have hs := (assemblyClockAtomEquivΓ hM9 B s).2
  have hs' := Finset.mem_erase.mp hs
  obtain ⟨hn, hp, he⟩ := parentClock_interior B.isBlock R (t 0)
    (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) _ hs'.2 hs'.1
  by_cases hpa : (assemblyClockAtomEquivΓ hM9 B s).1.toNode.parent hn = a
  · left
    refine ⟨?_, hn, hpa⟩
    rw [he, hpa]
    exact clLocalClock_upper R t _
  · right
    have hmem : (assemblyClockAtomEquivΓ hM9 B s).1.toNode.parent hn ∈ U.erase a :=
      Finset.mem_erase.mpr ⟨hpa, hp⟩
    refine ⟨(assemblyClockAtomEquivΓ hM9 B).symm ⟨_, hmem⟩, ?_, ?_⟩
    · unfold assemblyTimeConstraintsΓ
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hn, ?_⟩
      rw [Equiv.apply_symm_apply]
    · rw [he]
      have := clLocalClock_slotΓ hM9 B t τ ((assemblyClockAtomEquivΓ hM9 B).symm ⟨_, hmem⟩)
      rw [Equiv.apply_symm_apply] at this
      exact this

theorem constraint_parent_clockΓ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (c : (assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)
    (hc : c ∈ assemblyTimeConstraintsΓ hM9 B) :
    parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ))
        (assemblyClockAtomEquivΓ hM9 B c.1).1.toNode = τ c.2 := by
  classical
  unfold assemblyTimeConstraintsΓ at hc
  obtain ⟨_, hn, hp⟩ := Finset.mem_filter.mp hc
  rw [parentClock_nonroot _ _ _ hn, hp]
  exact clLocalClock_slotΓ hM9 B t τ c.2

end WaveTurbulence.GammaLow.Famb.VineEstS2
