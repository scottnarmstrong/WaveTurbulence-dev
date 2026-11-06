/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificatePhases
import Mathlib.Tactic

/-! # Exact shared FullVineChart from a checked finite normalized certificate

This is the generic certificate consumer. Source existence still requires
a concrete certificate producer and transport from the actual source vine.
-/

public section
namespace WaveTurbulence.Vine.Param.NormalizedVineCertificate
open Finset VineParamContract
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- The actual internal bond set has exactly2n individually marked bonds. -/
theorem bond_count :
    (internalBondSet (graphMolecule C.matrix.ends) univ).card=2*C.shape.n := by
  have h := Fintype.card_congr (graphBondEquiv C.matrix.ends)
  simpa only [Fintype.card_fin,Fintype.card_coe] using h.symm

/-- Actual-bond decoder free coefficients. -/
@[expose] noncomputable def decodeFree :
    Matrix (Bond (graphMolecule C.matrix.ends) univ) (Fin C.shape.n) ℤ :=
  fun e i => C.matrix.decodeFree ((graphBondEquiv C.matrix.ends).symm e) i

/-- The actual-bond integer gap coefficient. -/
@[expose] noncomputable def decodeGap : Bond (graphMolecule C.matrix.ends) univ → ℤ :=
  fun e => C.matrix.decodeGap ((graphBondEquiv C.matrix.ends).symm e)

/-- Every actual free coefficient is exactly0,1 or−1. -/
theorem free_unit : ∀ e i,UnitCoeff (C.decodeFree e i) := by
  intro e i
  have h := C.matrix.decodeFree_unit ((graphBondEquiv C.matrix.ends).symm e) i
  rcases mem_insert.mp h with h | h
  · exact Or.inr (Or.inr h)
  · rcases mem_insert.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_singleton.mp h))

/-- Exact affine inverse on the whole actual-bond source fiber. -/
theorem decode_eq {E : Type} [AddCommGroup E] (g r : E) (x : Fin C.shape.n → E)
    (e : Bond (graphMolecule C.matrix.ends) univ) :
    ((C.chart g r).symm x).1 e=g+(∑ i,C.decodeFree e i • x i)+C.decodeGap e • r := by
  rw [C.chart_decode]
  exact C.matrix.affineChart_decode_eq g r x ((graphBondEquiv C.matrix.ends).symm e)

/-- Every coordinate is a difference of fixed actual internal or boundary
labels, uniformly over all additive momentum groups. -/
theorem difference (i : Fin C.shape.n) :
    ∃ p q : Bond (graphMolecule C.matrix.ends) univ ⊕ Fin 2,
      ∀ {E : Type} [AddCommGroup E] (g r : E)
        (k : FlowFiber (graphMolecule C.matrix.ends) univ C.matrix.a C.matrix.b E r),
        C.chart g r k i=origin (graphMolecule C.matrix.ends) univ k.1 g r p-
          origin (graphMolecule C.matrix.ends) univ k.1 g r q := by
  by_cases hi : i=C.shape.x0
  · subst i
    refine ⟨.inr 0,.inl (graphBondEquiv C.matrix.ends C.joint.outgoing),?_⟩
    intro E _ g r k
    exact C.matrix.affineChart_reference_of_row C.shape.x0 C.joint.outgoing C.reference_row g r
      (graphContractFiber C.matrix.ends C.matrix.a C.matrix.b C.matrix.distinct r k)
  · let p := (C.differencePair ⟨i,hi⟩).1
    let q := (C.differencePair ⟨i,hi⟩).2
    refine ⟨.inl (graphBondEquiv C.matrix.ends p),.inl (graphBondEquiv C.matrix.ends q),?_⟩
    intro E _ g r k
    exact C.matrix.affineChart_difference_of_row i p q (C.difference_rows ⟨i,hi⟩) g r
      (graphContractFiber C.matrix.ends C.matrix.a C.matrix.b C.matrix.distinct r k)

/-- A checked finite integer certificate supplies exactly the shared V4
full-vine chart, including signed cores and the VII single-bond junction. -/
@[expose] noncomputable def fullChart :
    FullVineChart (graphMolecule C.matrix.ends) X univ C.matrix.a C.matrix.b where
  indexing := C.indexing
  bond_count := C.bond_count
  junction := C.junction
  junction_type := C.junction_type
  rung_bonds := C.rung_bonds
  decodeFree := C.decodeFree
  decodeGap := C.decodeGap
  free_unit := C.free_unit
  chart := C.chart
  decode_eq := C.decode_eq
  difference := C.difference
  ζc := C.ζ
  ζ_unit := C.ζ_unit
  ζ_bad_nonzero := C.ζ_bad_nonzero
  coreLinear := C.coreLinear
  coreFirstSign := C.coreFirstSign
  coreSign := C.coreSign
  ξc := C.ξ
  ξ_unit := C.ξ_unit
  joint_phase := C.joint_phase
  rung_t_phase := C.rung_t_phase
  rung_s_phase := C.rung_s_phase
  core_first_phase := C.core_first_phase
  core_second_phase := C.core_second_phase
  core_sum_phase := C.core_sum_phase

end WaveTurbulence.Vine.Param.NormalizedVineCertificate
