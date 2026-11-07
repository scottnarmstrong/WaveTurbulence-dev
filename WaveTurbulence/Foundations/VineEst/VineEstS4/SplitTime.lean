/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Splitting the internal times of `U = S ∪ T` (V5 Step 4b, P2.3 Fubini form)

`exists_timeSplit`: for `U = A ∪ B` (disjoint finsets) there is a volume-preserving measurable equivalence
`(A → ℝ) × (B → ℝ) ≃ (U → ℝ)` which restricts to the two components.  Locality of `spart`: it reads the clock only on
`S`, so `spart (clLocalClock RU t τ) = spart (clLocalClock RS t σ)` for `σ` the restriction of `τ` to `S.erase a`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

theorem exists_timeSplit {ι : Type*} [DecidableEq ι] (U A B : Finset ι) (h : U = A ∪ B) (hd : Disjoint A B) :
    ∃ e : (↥A → ℝ) × (↥B → ℝ) ≃ᵐ (↥U → ℝ), MeasurePreserving e volume volume ∧
      (∀ σ ρ (v : ι) (hv : v ∈ A), e (σ, ρ) ⟨v, h ▸ Finset.mem_union_left _ hv⟩ = σ ⟨v, hv⟩) ∧
      (∀ σ ρ (v : ι) (hv : v ∈ B), e (σ, ρ) ⟨v, h ▸ Finset.mem_union_right _ hv⟩ = ρ ⟨v, hv⟩) := by
  subst h
  exact ⟨MeasurableEquiv.piFinsetUnion (fun _ => ℝ) hd, volume_preserving_piFinsetUnion (fun _ => ℝ) hd,
    fun σ ρ v hv => Equiv.piFinsetUnion_left (fun _ => ℝ) hd hv _,
    fun σ ρ v hv => Equiv.piFinsetUnion_right (fun _ => ℝ) hd hv _⟩

end WaveTurbulence.VineEstS4
