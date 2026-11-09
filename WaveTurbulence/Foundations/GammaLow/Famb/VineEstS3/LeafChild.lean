/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.VineChainSumintForm
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3DataS1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild` (sha256 9b320aca5196d4dc…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Leaf lower children (TARGET vineest Step 3, the case `u_{21}` or `u_{22}` a leaf)

The kernel `K̃^U` does not depend on the time of an excluded lower child that is a leaf (`clLocalClock_congr`,
`clLocalTimeDomain_congr`, `clRecenteredLocalKernel_congr`), and the source clock domain is the `sumint` input domain
(up to a null set) as soon as the dummy time of a leaf child is at most the lower window end of the lower joint
(`assemblyTimeDomain_of_source'`, `integral_clockDomain_eq'`, `vineChain_eq_sumintForm'`, which drop `hb1/hb2` of V4).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree Reg WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

/-- Source clock domain `⊆` sumint input domain, when each excluded lower child is a branch or its (dummy) time is
at most the lower window end `q_b` of the lower joint (so `t' ≤ q_b < τ_b`). -/
theorem assemblyTimeDomain_of_source'Γ (hI : 0 < (assemblyShapeΓ hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQΓ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQΓ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (h : assemblyClockEquivΓ hM9 B τ ∈ clLocalTimeDomain R layerB t) :
    τ ∈ assemblyTimeDomainΓ hM9 B layerB hI t := by
  obtain ⟨hmain, hpos, hneg⟩ := h
  have hslot : ∀ s, (assemblyClockEquivΓ hM9 B τ) (assemblyClockAtomEquivΓ hM9 B s) = τ s :=
    fun s => assemblyClock_apply_slotΓ hM9 B t τ s
  have hlt : ∀ s, τ s < t 0 := by
    intro s
    have hs' := Finset.mem_erase.mp (assemblyClockAtomEquivΓ hM9 B s).2
    have hyp : ∀ v ∈ U, v ≠ a → clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v <
        parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) v.toNode := by
      intro v hv hva
      have hv' : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hva, hv⟩
      have e := clLocalClock_internal R t (assemblyClockEquivΓ hM9 B τ) ⟨v, hv'⟩
      have := (hmain ⟨v, hv'⟩).2.2.2
      rwa [← e] at this
    have h0 := interior_clock_lt_top B.isBlock R (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ))
      (clLocalClock_upper R t _) hyp _ _ rfl hs'.2 hs'.1
    rwa [clLocalClock_slotΓ hM9 B t τ s] at h0
  have hb : (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0,hI⟩,0⟩)).1 = b := assemblyClockAtom_firstΓ hM9 B hI
  have hbclock : clLocalClock R t (assemblyClockEquivΓ hM9 B τ) b = τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have := clLocalClock_slotΓ hM9 B t τ (.inl ⟨⟨0,hI⟩,0⟩)
    rwa [hb] at this
  have hw0 : (assemblyTimeQΓ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩) : ℝ) < τ (.inl ⟨⟨0,hI⟩,0⟩) := by
    have h := hmain (assemblyClockAtomEquivΓ hM9 B (.inl ⟨⟨0,hI⟩,0⟩))
    rw [hslot] at h
    exact h.1
  refine ⟨fun s => ?_, ?_, fun c hc => ?_⟩
  · have h := hmain (assemblyClockAtomEquivΓ hM9 B s)
    rw [hslot s] at h
    exact ⟨h.1.le, h.2.1.le, hlt s⟩
  · rw [max_lt_iff]
    refine ⟨?_, ?_⟩
    · rcases hp with hb1 | hle
      · rw [← hbclock]; exact hpos hb1
      · exact lt_of_le_of_lt hle hw0
    · rcases hn with hb2 | hle
      · rw [← hbclock]; exact hneg hb2
      · exact lt_of_le_of_lt hle hw0
  · have h1 := (hmain (assemblyClockAtomEquivΓ hM9 B c.1)).2.2.2
    rw [hslot c.1, constraint_parent_clockΓ hM9 B t τ c hc] at h1
    exact h1

theorem integral_clockDomain_eq'Γ (hI : 0 < (assemblyShapeΓ hM9 B).I) (layerB : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ)
    (hp : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      t 1 ≤ assemblyTimeQΓ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (hn : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      t 2 ≤ assemblyTimeQΓ hM9 B layerB (.inl ⟨⟨0,hI⟩,0⟩))
    (f : ((assemblyShapeΓ hM9 B).TVar → ℝ) → ℂ) :
    ∫ τ, (assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R layerB t).indicator f τ =
      ∫ τ in assemblyTimeDomainΓ hM9 B layerB hI t, f τ := by
  rw [← integral_indicator (measurableSet_assemblyTimeDomainΓ hM9 B hI layerB t)]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ, ∀ s, τ s ≠ assemblyTimeQΓ hM9 B layerB s ∧
      τ s ≠ assemblyTimeQΓ hM9 B layerB s + 1 := by
    rw [ae_all_iff]
    intro s
    exact (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _).and
      (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) s _)
  filter_upwards [hae] with τ hτ
  by_cases hmem : τ ∈ assemblyTimeDomainΓ hM9 B layerB hI t
  · rw [Set.indicator_of_mem hmem]
    exact Set.indicator_of_mem (s := assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R layerB t)
      (source_of_assemblyTimeDomainΓ hM9 B hI layerB t τ hmem hτ) f
  · rw [Set.indicator_of_notMem hmem]
    refine Set.indicator_of_notMem (s := assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R layerB t)
      (fun h => hmem ?_) f
    exact assemblyTimeDomain_of_source'Γ hM9 B hI layerB t τ hp hn h

end WaveTurbulence.GammaLow.Famb.VineEstS3
