/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificateFullChart
import Mathlib.Tactic

/-! # Physical origins retained as induction data for source chart construction

These are strengthened data for chart composition, not additional hypotheses
in the final source-facing VINEPARAM obligation.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

/-- A previously constructed full chart with its fixed physical reference
and internal difference representatives. -/
structure PhysicalGraphChart {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β]
    (ends : β → V×V) (X : VineType) (a b : V) where
  distinct : a ≠ b
  full : FullVineChart (graphMolecule ends) X univ a b
  reference : β
  reference_at : (ends reference).1=b ∨ (ends reference).2=b
  reference_eq : ∀ {E : Type} [AddCommGroup E] (g r : E)
    (k : FlowFiber (graphMolecule ends) univ a b E r),
    full.chart g r k full.indexing.shape.x0=g-k.1 (graphBondEquiv ends reference)
  reference_column : ∀ e,full.decodeFree e full.indexing.shape.x0= -1
  differencePair : {i : Fin full.indexing.shape.n // i ≠ full.indexing.shape.x0} → β×β
  difference_eq : ∀ i,∀ {E : Type} [AddCommGroup E] (g r : E)
    (k : FlowFiber (graphMolecule ends) univ a b E r),
    full.chart g r k i.1=k.1 (graphBondEquiv ends (differencePair i).1)-
      k.1 (graphBondEquiv ends (differencePair i).2)

namespace NormalizedVineCertificate
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- Every checked normalized base certificate supplies the fixed physical
origins and exact reference column used by the insertion induction. -/
@[expose] noncomputable def physicalChart :
    PhysicalGraphChart C.matrix.ends X C.matrix.a C.matrix.b where
  distinct := C.matrix.distinct
  full := C.fullChart
  reference := C.joint.outgoing
  reference_at := Or.inl C.joint.outgoing_at
  reference_eq := by
    intro E _ g r k
    exact C.matrix.affineChart_reference_of_row C.shape.x0 C.joint.outgoing C.reference_row g r
      (graphContractFiber C.matrix.ends C.matrix.a C.matrix.b C.matrix.distinct r k)
  reference_column := by
    intro e
    exact C.matrix.decodeFree_reference ((graphBondEquiv C.matrix.ends).symm e)
  differencePair := C.differencePair
  difference_eq := by
    intro i E _ g r k
    exact C.matrix.affineChart_difference_of_row i.1 (C.differencePair i).1 (C.differencePair i).2
      (C.difference_rows i) g r
      (graphContractFiber C.matrix.ends C.matrix.a C.matrix.b C.matrix.distinct r k)

end NormalizedVineCertificate
end WaveTurbulence.Vine.Param
