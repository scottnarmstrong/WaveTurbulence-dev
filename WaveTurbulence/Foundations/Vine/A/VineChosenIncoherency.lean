/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationSplice
public import WaveTurbulence.Foundations.Molecule.VineCoherenceIndependent
/-! The actual chosen vine incoherency index is independent of template,
ordered-joint choices and actual molecular relabeling. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Vine
variable {w : ℕ} {G H : Garden w}

/-- Realizations on the same actual atom set have equal indices, including swapped ordered joints. -/
theorem realized_index_eq_of_atoms {X Y : VineType} {S : Finset (GBranch G.tree)}
    {a b c d : GBranch G.tree} (R : VineRealization G.molecule X S a b)
    (T : VineRealization G.molecule Y S c d) (hB : G.molecule.IsBlock S a b)
    (hC : G.molecule.IsBlock S c d) (layer : GBranch G.tree → ℕ) :
    realizedIncoherencyIndex R layer = realizedIncoherencyIndex T layer := by
  have hj := Vine.block_joints_unique G.molecule hB hC
  have hf : ({T.f a, T.f b} : Finset ℕ) = {0, 1} := by
    have h := congrArg (Finset.image T.f) hj
    simp only [Finset.image_insert, Finset.image_singleton] at h
    exact h.trans T.joints_eq
  let T' : VineRealization G.molecule Y S a b :=
    ⟨T.k, T.length_eq, T.f, T.injOn, T.image_eq, hf, T.bonds_eq⟩
  exact realizedIncoherencyIndex_eq G.molecule (Mole.garden_isMolecule G) R T' hB layer

end WaveTurbulence.VineA
