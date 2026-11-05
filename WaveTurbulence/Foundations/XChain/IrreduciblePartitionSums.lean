/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionExpansion
/-! The source irreducible-partition filter and its actual subtype carrier give the same finite sum. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem sum_irreducible_partitions {w : ℕ} (top : Fin w → TTree)
    (f : Finpartition (univ : Finset (GLeaf top)) → ℂ) :
    (∑ P : {P : Finpartition (univ : Finset (GLeaf top)) // TopPartitionIrreducible top P}, f P.1) =
      ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter (TopPartitionIrreducible top), f P := by
  rw [CumulantProducts.sum_subtype_eq_sum_ite, Finset.sum_filter]

end WaveTurbulence.Induct
