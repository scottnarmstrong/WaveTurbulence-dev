/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSingleCoreEdges
import Mathlib.Tactic

/-! # Actual old-label single edges, independent of a chosen core-atom expression -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Any retained old-core single pair is intrinsically a single actual
edge. Only source labels, pair counts and actual adjacency are consumed. -/
theorem VineRealization.old_single_of_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hu : u ∈ S) (hv : v ∈ S) (huold : R.f u<X.template.n)
    (hvold : R.f v<X.template.n) (hne : R.f u ≠ R.f v)
    (hc : X.template.bonds.count (R.f u,R.f v)+X.template.bonds.count (R.f v,R.f u)=1)
    (ha : M.Adj u v) : SingleGroupAdj M S u v := by
  have huv : u ≠ v := fun h => hne (congrArg R.f h)
  have hd := R.old_pair_degree_le hu hv huv huold hvold
  rw [hc] at hd
  have hp := pair_degree_pos_of_adj M ha
  exact ⟨hu,hv,huv,ha,by omega⟩

end WaveTurbulence.Vine
