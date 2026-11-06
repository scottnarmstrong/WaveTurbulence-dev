/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.GardenDecorationEquiv
import Mathlib.Tactic

/-!
# Correspondence against the exact B2 lattice-decoration predicate

TARGET `defdecmol`, with F52 root-pair compatibility. No alternate molecule
or decoration predicate is substituted for the pinned B2 definitions.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w d : ℕ} (G : Garden w)

/-- Actual integer labels are determined by their affine lattice vectors
at every nonzero scale. -/
theorem kvec_injective {L : ℝ} (hL : L ≠ 0) (base : Mom d) :
    Function.Injective (fun z : Fin d → ℤ => base + latticePoint L z) := by
  intro z z' he
  have hv := add_left_cancel he
  funext i
  have hi := congrArg (fun v : Mom d => v i) hv
  change (z i : ℝ)/L = (z' i : ℝ)/L at hi
  exact Int.cast_injective ((div_left_inj' hL).mp hi)

/-- Every actual B2 molecule decoration extends to a garden decoration,
with exactly its prescribed roots and bond labels (F52). -/
theorem gardenDecoration_of_molecule (hP : G.IsPlain) (n : Fin w → Mom d)
    (hn : RootPairCompatible G n) (L : ℝ) (base : Mom d)
    (k : GardenDart G → (Fin d → ℤ))
    (hk : G.molecule.IsDecoration L base (gardenSource G hP n) k) :
    let κ := extendLabels G hP n (Molecule.kvec L base k)
    IsDecoration G κ ∧ (∀ i, κ (GNode.root G.tree i) = n i) ∧
      restrictLabels G κ = Molecule.kvec L base k := by
  have hm : ∀ x, Molecule.kvec L base k (G.molecule.mate x) = Molecule.kvec L base k x := by
    intro x
    simp only [Molecule.kvec,hk.1 x]
  have hh : ∀ v, ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base k x =
      gardenSource G hP n v := fun v => hk.2 v (Finset.mem_univ _)
  let he := (gardenDecorationEquiv G hP n hn).symm ⟨Molecule.kvec L base k,hm,hh⟩
  exact ⟨he.2.1,he.2.2,restrict_extendLabels G hP n _ hm⟩

/-- Conversely, restricting an affine-lattice garden decoration gives an
actual B2 molecule decoration with the source boundary vector. -/
theorem moleculeDecoration_of_garden (hP : G.IsPlain) (n : Fin w → Mom d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (hκ : IsDecoration G (fun a => base + latticePoint L (κ a)))
    (hr : ∀ i, base + latticePoint L (κ (GNode.root G.tree i)) = n i) :
    G.molecule.IsDecoration L base (gardenSource G hP n) (restrictLabels G κ) := by
  have hn := rootPairCompatible_of_labels G n (fun a => base + latticePoint L (κ a)) hr hκ.2
  let he := (gardenDecorationEquiv G hP n hn) ⟨_,hκ,hr⟩
  refine ⟨?_,?_⟩
  · intro x
    apply kvec_injective hL base
    exact he.2.1 x
  · intro v _hv
    exact he.2.2 v

/-- On fixed-root garden decorations, incidence restriction loses no node
values: the extension recovers even nodes next to trivial trees. -/
theorem garden_vectors_determined_by_bonds (hP : G.IsPlain) (n : Fin w → Mom d)
    (κ κ' : GNode G.tree → Mom d) (hκ : IsDecoration G κ) (hκ' : IsDecoration G κ')
    (hr : ∀ i, κ (GNode.root G.tree i) = n i)
    (hr' : ∀ i, κ' (GNode.root G.tree i) = n i)
    (he : restrictLabels G κ = restrictLabels G κ') : κ = κ' := by
  rw [← extend_restrictLabels G hP n κ hr hκ.2,
    ← extend_restrictLabels G hP n κ' hr' hκ'.2,he]

end WaveTurbulence.Mole
