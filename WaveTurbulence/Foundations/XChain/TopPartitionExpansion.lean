/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopLeafGroups
/-! propertycm on the literal top-tree leaf groups, transported to partitions of the whole leaf set. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped Classical

def TopPartitionIrreducible {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) : Prop :=
  ∀ A ⊆ (univ : Finset (Fin w)), A.Nonempty → A ≠ univ →
    ¬∃ B : Finset (Finset (GLeaf top)), B ⊆ P.parts ∧
      A.biUnion (topLeafGroups top) = B.biUnion id

theorem topPartitionIrreducible_equiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition ((univ : Finset (Fin w)).biUnion (topLeafGroups top))) :
    TopPartitionIrreducible top (topPartitionEquiv top P) ↔
      IsIrreduciblePartition univ (topLeafGroups top) P := by
  simp only [TopPartitionIrreducible, IsIrreduciblePartition, topPartitionEquiv_parts]

/-- The exact irreducible-partition expansion of the products at the top roots. -/
theorem cumulant_top_leaf_groups {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w : ℕ} (top : Fin w → TTree) (X : GLeaf top → Ω → ℂ) :
    cumulant μ (fun j ω => ∏ a ∈ topLeafGroups top j, X a ω) univ =
      ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter
          (TopPartitionIrreducible top), ∏ B ∈ P.parts, cumulant μ X B := by
  rw [cumulant_prod μ X univ (topLeafGroups top) (topLeafGroups_disjoint top)
    (fun j _ => topLeafGroups_nonempty top j)]
  simp only [Finset.sum_filter]
  exact Fintype.sum_equiv (topPartitionEquiv top) _ _ (fun P => by
    simp only [topPartitionEquiv_parts, topPartitionIrreducible_equiv])

end WaveTurbulence.Induct
