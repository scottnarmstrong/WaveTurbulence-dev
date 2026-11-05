/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules

/-!
# Degree-only block and vine predicates (UNIVERSE compatibility)

The legacy MOLE-era block/vine predicates, kept under the names `IsBlockDeg` and `IsVineDeg` as in the M6 (molecpl)
packet. Bodies are the legacy ones (no connectedness conjunct). The canonical `IsBlock`/`IsVine` imply them
(`WaveTurbulence.Molecpl.isBlock_degree`, `isVine_degree` in `CurrentBlockBridge`); no canonical definition is changed.
-/

@[expose] public section
namespace WaveTurbulence
namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

def IsBlockDeg (S : Finset V) (j₁ j₂ : V) : Prop :=
  S ⊆ M.atoms ∧ j₁ ∈ S ∧ j₂ ∈ S ∧ j₁ ≠ j₂ ∧
    M.outIn S j₁ = 1 ∧ M.inIn S j₁ = 1 ∧ M.outIn S j₂ = 1 ∧ M.inIn S j₂ = 1 ∧
    ∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → M.degIn S v = 4

instance (S : Finset V) (j₁ j₂ : V) : Decidable (M.IsBlockDeg S j₁ j₂) := by
  unfold IsBlockDeg
  infer_instance

def IsVineDeg (X : VineType) (S : Finset V) (j₁ j₂ : V) : Prop :=
  M.IsBlockDeg S j₁ j₂ ∧ ∃ k : List ℕ, k.length = X.template.slots.length ∧
    ∃ f : V → ℕ, Set.InjOn f S ∧ S.image f = Finset.range (X.expand k).n ∧
      ({f j₁, f j₂} : Finset ℕ) = {0, 1} ∧
      (M.groupBonds S).map (Sym2.map f) = ((X.expand k).bonds.map fun p => s(p.1, p.2) : Multiset _)

end Molecule
end WaveTurbulence
