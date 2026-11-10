/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Phase integrals of plain gardens are ordinary integrals over all branching times. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory

theorem not_flowerParent_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, _⟩
  have hm := hG ℓ
  have he := hm.symm.trans hℓ
  cases he

noncomputable def freeBranchEquivOfNoFlowerParent {w : ℕ} (G : Garden w)
    (hG : ∀ b, ¬ G.IsFlowerParent b) : G.FreeBranch ≃ GBranch G.tree :=
  Equiv.subtypeUnivEquiv hG

end WaveTurbulence.LGSpine
