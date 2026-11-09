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
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Weights
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
open WaveTurbulence.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The input time domain of `sumint` with the source layers and parent order. -/
def assemblyTimeDomainΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (layerB : GBranch G.tree → ℕ)
    (hI : 0 < (assemblyShapeΓ hM9 B).I) (t : Fin 3 → ℝ) : Set ((assemblyShapeΓ hM9 B).TVar → ℝ) :=
  {τ | (∀ s, (assemblyTimeQΓ hM9 B layerB s : ℝ) ≤ τ s ∧ τ s ≤ assemblyTimeQΓ hM9 B layerB s + 1 ∧
      τ s < t 0) ∧
    max (t 1) (t 2) < τ (.inl ⟨⟨0,hI⟩,0⟩) ∧ ∀ c ∈ assemblyTimeConstraintsΓ hM9 B, τ c.1 < τ c.2}

variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

theorem assemblyClock_apply_slotΓ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (s : (assemblyShapeΓ hM9 B).TVar) :
    assemblyClockEquivΓ hM9 B τ (assemblyClockAtomEquivΓ hM9 B s) = τ s :=
  (clLocalClock_internal R t (assemblyClockEquivΓ hM9 B τ) _).symm.trans (clLocalClock_slotΓ hM9 B t τ s)

/-- Conversely, off the unit-interval boundaries the sumint input time domain lies in the source
clock domain. -/
theorem source_of_assemblyTimeDomainΓ (hI : 0 < (assemblyShapeΓ hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (hτ : τ ∈ assemblyTimeDomainΓ hM9 B layerB hI t)
    (hbd : ∀ s, τ s ≠ assemblyTimeQΓ hM9 B layerB s ∧ τ s ≠ assemblyTimeQΓ hM9 B layerB s + 1) :
    assemblyClockEquivΓ hM9 B τ ∈ clLocalTimeDomain R layerB t := by
  obtain ⟨hwin, hjoin, hcon⟩ := hτ
  have hb : (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := assemblyClockAtom_firstΓ hM9 B hI
  have hbclock : clLocalClock R t (assemblyClockEquivΓ hM9 B τ) b = τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have := clLocalClock_slotΓ hM9 B t τ (.inl ⟨⟨0,hI⟩,0⟩)
    rwa [hb] at this
  refine ⟨fun v => ?_, fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨s, rfl⟩ := (assemblyClockAtomEquivΓ hM9 B).surjective v
    have hv : clLocalClock R t (assemblyClockEquivΓ hM9 B τ) (assemblyClockAtomEquivΓ hM9 B s).1 = τ s :=
      clLocalClock_slotΓ hM9 B t τ s
    have e1 : (assemblyClockEquivΓ hM9 B τ) (assemblyClockAtomEquivΓ hM9 B s) = τ s :=
      assemblyClock_apply_slotΓ hM9 B t τ s
    obtain ⟨h1, h2, h3⟩ := hwin s
    have hq0 : (0 : ℝ) ≤ assemblyTimeQΓ hM9 B layerB s := Nat.cast_nonneg _
    have hlow : (assemblyTimeQΓ hM9 B layerB s : ℝ) < τ s := lt_of_le_of_ne h1 (hbd s).1.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; exact hlow
    · rw [e1]; exact lt_of_le_of_ne h2 (hbd s).2
    · rw [e1]; exact hq0.trans_lt hlow
    · rw [e1]
      rcases slot_parent_clockΓ hM9 B t τ s with ⟨hp, _⟩ | ⟨s', hs', hp⟩
      · rw [hp]; exact h3
      · rw [hp]; exact hcon _ hs'
  · rw [hbclock]
    exact (le_max_left _ _).trans_lt hjoin
  · rw [hbclock]
    exact (le_max_right _ _).trans_lt hjoin

theorem measurableSet_assemblyTimeDomainΓ (hI : 0 < (assemblyShapeΓ hM9 B).I)
    (layerB : GBranch G.tree → ℕ) (t : Fin 3 → ℝ) :
    MeasurableSet (assemblyTimeDomainΓ hM9 B layerB hI t) := by
  unfold assemblyTimeDomainΓ
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun s => ?_) (MeasurableSet.inter ?_
    (MeasurableSet.iInter fun c => MeasurableSet.iInter fun hc => ?_))
  · refine MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop))
      (MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop))
        (measurableSet_lt (by fun_prop) (by fun_prop)))
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)

end WaveTurbulence.GammaLow.Famb.VineEstS2
