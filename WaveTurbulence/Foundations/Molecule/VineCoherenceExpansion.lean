/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoherence
public import WaveTurbulence.Foundations.Molecule.VineGroupPartition

/-! # Coherence of the exact expanded group decomposition (TARGET cohmol) -/

public section
namespace WaveTurbulence.Vine
variable {L : Type*} [DecidableEq L]

/-- The source vine incoherency index on a chosen exact template realization. -/
@[expose] def vineIncoherencyIndex (X : VineType) (k : List ℕ) (layer : ℕ → L) : ℕ :=
  incoherencyIndex layer (X.expand k).groups

/-- The source coherence predicate on the same realization. -/
@[expose] def VineCoherent (X : VineType) (k : List ℕ) (layer : ℕ → L) : Prop :=
  Coherent layer (X.expand k).groups

/-- TARGET cohmol: the index counts at most one defect per group. -/
theorem vineIncoherencyIndex_le (X : VineType) (k : List ℕ) (layer : ℕ → L)
    (hk : k.length=X.template.slots.length) :
    vineIncoherencyIndex X k layer ≤ X.template.groups.length+k.sum := by
  exact (incoherencyIndex_le layer _).trans_eq (expand_groups_exact X k hk)

/-- TARGET cohmol: coherence is precisely index zero. -/
theorem vineIncoherencyIndex_eq_zero_iff (X : VineType) (k : List ℕ) (layer : ℕ → L) :
    vineIncoherencyIndex X k layer=0 ↔ VineCoherent X k layer :=
  incoherencyIndex_eq_zero_iff layer _

end WaveTurbulence.Vine
