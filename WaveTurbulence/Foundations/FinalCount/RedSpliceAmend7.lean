/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal
public import WaveTurbulence.Foundations.FinalCount.RedSpliceTripleHinge
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R48 AMEND7 producer obligations

the proofs that `collectionChoices S σ` satisfies `SubproChoices.TripleDesignated` and `HingeNoLoop` (in lg-spine `SourceSubproObjects` since AMEND7):
* `tripleDesignated_collectionChoices` (R37 `triple_in_hingePair`, TARGET subpro (2),(5), DH23 L1775 (iii));
* `hingeNoLoop_collectionChoices` (`SpMap.od_range`: a dart of `G_sb` never has both ends in one merged class).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false

namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- `collectionChoices G σ` satisfies `TripleDesignated` (term of S4's `triple_in_designated`, via
`triple_in_hingePair`; no S4 import). -/
theorem tripleDesignated_collectionChoices {G : Garden w} (hM : G.molecule.IsMolecule)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) (σ : Prescription G) :
    (collectionChoices G σ).TripleDesignated := by
  intro a b h
  rcases (stSt G σ).triple_hinge hno a b h with ha | hb
  · obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePair hM σ ha h
    exact ⟨a, ha, b, x, y, Or.inl ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩
  · have h' : (stSt G σ).G.molecule.bondsBetween b a = 3 := by
      rw [Mole.bondsBetween_symm]; exact h
    obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePair hM σ hb h'
    exact ⟨b, hb, a, x, y, Or.inr ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩

/-- No loop dart at a hinge of `G_sb`: both ends of a dart of `G_sb` never lie in one merged class (`od_range`). -/
theorem hingeNoLoop_collectionChoices {G : Garden w} (σ : Prescription G) :
    (collectionChoices G σ).HingeNoLoop := by
  intro x hx hloop
  have hcn := ((stSt G σ).mem_hinges _).mp hx
  have hr := ((stSt G σ).M.od_range ((stSt G σ).M.od x)).mp ⟨x, rfl⟩
  have h1 := (stSt G σ).M.ob_atom x
  have h2 := (stSt G σ).M.ob_atom ((stSt G σ).G.molecule.mate x)
  rw [(stSt G σ).M.od_mate] at h2
  rw [← hloop] at h2
  set p := G.molecule.atom ((stSt G σ).M.od x)
  set q := G.molecule.atom (G.molecule.mate ((stSt G σ).M.od x))
  have hp : (stSt G σ).cls p ≠ none := by
    intro hn
    apply hcn
    rw [h1]; simp [repC, hn]
  have hq : (stSt G σ).cls q ≠ none := by
    intro hn
    apply hcn
    rw [h2]; simp [repC, hn]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hq
  have hab : a = b := by
    have e : repC (stSt G σ).cls p = repC (stSt G σ).cls q := h1.symm.trans h2
    simp [repC, ha, hb] at e; exact e
  exact hr ⟨a, ha, hab ▸ hb⟩

end WaveTurbulence.RedSplice
