/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
/-! # Named inputs of packet L5a (GH-COMMON "Named inputs")

Results owned by other packets that do not exist yet, stated exactly as the refereed notes state them, under names
distinct from any source theorem. They are hypotheses of L5a's internal theorems; wt-orch discharges them at assembly.

- `VinechainlemPrimeInput` (owner L3, "Lemma 8.1′ (DV′)"): TARGET Lemma `vinechainlem` (L1930–L1933; DH23 Lemma 8.1)
  with `DV` replaced by `DV′` = the union of two `σ = 1` members of `𝒱_γ` sharing both joints and no other atom
  (N2 N6, research-gamma-half-2/NOTES.md L978–L983; REFEREED by research-gamma-half-referee-2/REPORT.md; PLAN §2a T5,
  D3). Stated in the form of main's `LGSpine.VinePartitionGate` (FinalCount/SourceVinePartitionInput.lean), for the
  family `𝒱_γ` with `γ ≤ 1/2`. Body-identical to L3's `TVine.Struct.VinechainStatement` (at universe 0).
- `TVineF1Input` (owner L3, N2 Theorem 1.15 (F1), all sizes; research-gamma-half-2/NOTES.md Thm 1.15, REF2 R1 patch in
  N3 §2.1; restated in M4 §2.2): for a T-vine `(S, j₁, j₂)`, `S ∖ {j₁, j₂}` is connected (DH23 `disjointlem` (i)) and
  `S ∖ {v}` is connected for every interior `v` (no interior cut vertex, (ii)). Body-identical to the first two
  conjuncts of L3's `TVine.Struct.SubObjectsStatement`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama

/-- **NAMED INPUT (L3; N2 N6, Lemma 8.1′).** For `γ ≤ 1/2` and any molecule there is a unique collection of disjoint
atomic groups, each an HV, VC, HVC or DV′ over `𝒱_γ`, such that any vine-like object is a subset of one of them. -/
def VinechainlemPrimeInput : Prop :=
  ∀ γ : ℝ, γ ≤ 1 / 2 → ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ M : Molecule V D, M.IsMolecule → ∃! collection, IsSourceVinePartitionG γ M collection

/-- **NAMED INPUT (L3; N2 Theorem 1.15 (F1)).** The interior of a T-vine is connected, and the T-vine has no interior
cut vertex. -/
def TVineF1Input : Prop :=
  ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      M.GroupConnected ((S.erase j₁).erase j₂) ∧
      (∀ w ∈ S, w ≠ j₁ → w ≠ j₂ → M.GroupConnected (S.erase w))

/-- Under `VinechainlemPrimeInput`, the maximal groups are the `vinechainlem′` collection. -/
theorem maximalGroupsG_isPartition (h : VinechainlemPrimeInput) {γ : ℝ} (hγ : γ ≤ 1 / 2) {V D : Type}
    [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (hM : M.IsMolecule) :
    IsSourceVinePartitionG γ M (maximalGroupsG γ M) := by
  obtain ⟨C, hC, -⟩ := h γ hγ V D M hM
  exact maximalGroups_isPartition hC

/-- `VinechainlemPrimeInput` and `γ ≤ 1/2`, carried as instances (`Fact`): the maximal groups are the
`vinechainlem′` collection. -/
theorem maximalGroupsG_partition [hV : Fact VinechainlemPrimeInput] {γ : ℝ} [hγ : Fact (γ ≤ 1 / 2)] {V D : Type}
    [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (hM : M.IsMolecule) :
    IsSourceVinePartitionG γ M (maximalGroupsG γ M) :=
  maximalGroupsG_isPartition hV.out hγ.out hM

end WaveTurbulence.GammaLow.Fama
