/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (4): the main theorem

`unitGap_of_selOf`: the SG gap clause (`VineB.UnitGap`) of every unit of `unitBlocks G σ` on a decoration `z` of a plain
molecule garden with the prescription restriction `selOf (ofPrescription σ)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- **UnitGap.**  For a decoration `z` of `G` with `selOf σ`, every unit of `unitBlocks G σ` has an SG boundary gap. -/
theorem unitGap_of_selOf (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hsel : selOf (GroupPrescription.ofPrescription σ) L γ η base z.1) {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ) :
    UnitGap L γ η (fun i => base + latticePoint L (z.1 (bnodes u i))) := by
  classical
  obtain ⟨Sg, hSg, hσ, hu'⟩ := mem_unitBlocks.mp hu
  obtain ⟨a, O, -, hO, hdes⟩ := designatedObject_spec hSg
  have hκ := spliced_molecule_decoration G hp hL base roots z
  have hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      gardenSource G hp (fun i => base + latticePoint L (roots i)) v = 0 :=
    fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv
  obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z.1) hO
  have hkσ : k = Molecule.GapKind.SG := by
    rw [← hgk]
    exact (hsel ⟨Sg, hSg⟩).trans hσ
  subst hkσ
  obtain ⟨p, hsp⟩ := exists_unitSpec hu'
  have hgap := unitSpec_gapKind hM L γ η base _ _ hκ hc0 hu' hsp hdes hk
  obtain ⟨j, hj, hx, hy⟩ := unitSpec_joint hu' hsp
  obtain ⟨j', hj', hT, hn1, hn2, hrel⟩ := hsp
  have hxy : p.1 ≠ p.2 := fun h => hT.2.2.2 (by rw [h])
  have hnodes := extPair_nodes u hj hx hy hn1 hn2 hxy
  refine unitGap_of_cases L γ η _ _ hgap ?_ (boundary_diff_cases u L base z.1 z.2.1)
  have hr : Molecule.gapAt L base (bondIndex G z.1) p.1 p.2 =
      (base + latticePoint L (z.1 (dartNode G p.1))) - (base + latticePoint L (z.1 (dartNode G p.2))) := by
    simp only [Molecule.gapAt, Molecule.kvec, bondIndex_eq_dartNode]
  rw [hr]
  rcases hnodes with ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> rw [h1, h2]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end WaveTurbulence.Represents
