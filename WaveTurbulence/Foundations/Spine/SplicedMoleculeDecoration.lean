/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.Spine.KernelCosetDecoration
public import WaveTurbulence.Foundations.Spine.GardenEnergyCorrespondence
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
/-! The literal spliced decorations satisfy the exact molecular charge and energy predicates. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Mole

theorem bondIndex_eq_restrictLabels {w d : ℕ} (G : Garden w)
    (z : GNode G.tree → (Fin d → ℤ)) : bondIndex G z = restrictLabels G z := by
  funext x
  cases x <;> rfl

theorem bondIndex_injective {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (roots : Fin w → (Fin d → ℤ)) :
    Function.Injective (fun z : GenDecoration G d roots 0 => bondIndex G z.1) := by
  intro z z' he
  apply Subtype.ext
  change bondIndex G z.1 = bondIndex G z'.1 at he
  rw [bondIndex_eq_restrictLabels, bondIndex_eq_restrictLabels] at he
  rw [← extend_restrictLabels G hp roots z.1 z.2.2.1 z.2.1.2,
    ← extend_restrictLabels G hp roots z'.1 z'.2.2.1 z'.2.1.2, he]

theorem spliced_molecule_decoration {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) :
    G.molecule.IsDecoration L base
      (gardenSource G hp (fun i => base + latticePoint L (roots i))) (bondIndex G z.1) := by
  rw [bondIndex_eq_restrictLabels]
  apply moleculeDecoration_of_garden G hp _ hL base z.1
  · exact isDecoration_cosetDecoration G L base z.1 z.2.1
  · intro i
    rw [z.2.2.1 i]

theorem spliced_molecule_Gamma {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (v : GBranch G.tree) :
    G.molecule.Gamma L base (bondIndex G z.1) v =
      -(((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G (cosetDecoration G L base z.1) v +
        gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) v := by
  let n := fun i => base + latticePoint L (roots i)
  have hκ := isDecoration_cosetDecoration G L base z.1 z.2.1
  have hr : ∀ i, cosetDecoration G L base z.1 (GNode.root G.tree i) = n i := by
    intro i
    change base + latticePoint L (z.1 (GNode.root G.tree i)) = _
    rw [z.2.2.1 i]
  have hn := rootPairCompatible_of_labels G n _ hr hκ.2
  have hk := spliced_molecule_decoration G hp hL base roots z
  have hrestrict : restrictLabels G (cosetDecoration G L base z.1) =
      Molecule.kvec L base (bondIndex G z.1) := by
    funext x
    cases x <;> rfl
  have he := extend_restrictLabels G hp n (cosetDecoration G L base z.1) hr hκ.2
  rw [hrestrict] at he
  have hh := garden_molecule_Gamma G hp n hn L base (bondIndex G z.1) hk v
  dsimp only at hh
  rw [he] at hh
  exact hh

end WaveTurbulence.LGSpine
