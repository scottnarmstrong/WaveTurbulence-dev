/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Spine.Stage1Interface

/-!
# FLOWER-P1: the garden-side stub kernel (design C, R61 X4)

`kernelLeavesFix` generalizes `LGSpine.kernelLeaves` (the leafwise garden kernel with individual profiles
`H` at the input leaves) by designated *stub* nodes `fix : GBranch → Option ℝ`: a node with `fix b = some v`
has the prescribed time `v` and is not integrated, and `kDomainFix` keeps the order constraint between a
parent and a child iff at least one of the two is free.  With `fix ≡ none` on a plain garden it is
`kernelLeaves` (`kernelLeavesFix_noStubs`); likewise `LeafFamily.valueFix`, `valueSelFix` reduce to
`LeafFamily.value`, `valueSel`.

Anchors are trivial trees with prescribed root labels (the entries of `nroot`), paired with a stub child
leaf; their profile is `1` (`AnchorOne`).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset Set

namespace WaveTurbulence.FlowerP1

open WaveTurbulence LGSpine

/-- Integrals over function spaces on two subtypes defined by equivalent predicates agree. -/
theorem integral_subtype_congr {ι : Type*} [Fintype ι] {Pp Q : ι → Prop} [DecidablePred Pp]
    [DecidablePred Q] (h : ∀ i, Pp i ↔ Q i) (G : ({i // Q i} → ℝ) → ℂ) :
    ∫ τ : {i // Pp i} → ℝ, G (fun q => τ ⟨q.1, (h q.1).2 q.2⟩) = ∫ σ : {i // Q i} → ℝ, G σ := by
  let e : {i // Pp i} ≃ {i // Q i} := Equiv.subtypeEquivRight h
  have hmp := measurePreserving_piCongrLeft (fun _ : {i // Q i} => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : {i // Q i} => ℝ) e) G
  convert this using 2 with τ
  funext τ
  congr 1

/-- The designated times of a stub set: every stub gets the time `s`. -/
def stubFix {w : ℕ} {tree : Fin w → TTree} (stubs : Finset (GBranch tree)) (s : ℝ) :
    GBranch tree → Option ℝ := fun b => open Classical in if b ∈ stubs then some s else none

variable {w d : ℕ}

/-- The summand (without the prefactor `coupling ^ order * zeta`) of the stub kernel. -/
noncomputable def kernelLeavesFixTerm (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG up fix).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) *
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-! ## Bridges: no stubs, plain garden -/

end WaveTurbulence.FlowerP1
