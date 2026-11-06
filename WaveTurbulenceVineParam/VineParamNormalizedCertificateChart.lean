/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificateRows
import Mathlib.Tactic

/-! # Complete actual-bond chart supplied by a normalized finite certificate -/

public section
namespace WaveTurbulence.Vine.Param.NormalizedVineCertificate
open Finset VineParamContract
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- The exact contract included-atom indexing is the actual certificate
indexing, converted only between inequality and finite-set deletion. -/
@[expose] noncomputable def indexing :
    Indexing (graphMolecule C.matrix.ends) X univ C.matrix.a C.matrix.b where
  shape := C.shape
  atom := C.atom.trans (erasedUnivEquiv C.matrix.a).symm
  lower := C.lower

/-- The entire actual-bond source fiber is parametrized by the normalized
integer chart, over arbitrary additive groups and every prescribed gap. -/
@[expose] noncomputable def chart {E : Type} [AddCommGroup E] (g r : E) :
    FlowFiber (graphMolecule C.matrix.ends) univ C.matrix.a C.matrix.b E r ≃ (Fin C.shape.n → E) :=
  (graphContractFiber C.matrix.ends C.matrix.a C.matrix.b C.matrix.distinct r).trans
    (C.matrix.affineChart g r)

/-- The exact actual label decoded at a contract bond. -/
theorem chart_decode {E : Type} [AddCommGroup E] (g r : E) (x : Fin C.shape.n → E)
    (e : Bond (graphMolecule C.matrix.ends) univ) :
    ((C.chart g r).symm x).1 e=
      ((C.matrix.affineChart g r).symm x).1 ((graphBondEquiv C.matrix.ends).symm e) := rfl

/-- The actual included atom at any coordinate is unchanged by the finite-set conversion. -/
theorem indexing_atom (i : Fin C.shape.n) : (C.indexing.atom i).1=(C.atom i).1 := rfl

/-- Every nonreference included atom is a genuine interior source atom. -/
theorem atom_interior (i : Fin C.shape.n) (hi : i ≠ C.shape.x0) :
    (C.atom i).1 ≠ C.matrix.a ∧ (C.atom i).1 ≠ C.matrix.b := by
  refine ⟨(C.atom i).2,?_⟩
  intro hb
  have he : C.atom i=C.atom C.shape.x0 := Subtype.ext (hb.trans C.lower.symm)
  exact hi (C.atom.injective he)

/-- Contract energy and the actual normalized integer source energy agree. -/
theorem chart_energy {d : ℕ} (g r : Mom d) (x : Fin C.shape.n → Mom d) (v : Fin (C.shape.n+1)) :
    energy (graphMolecule C.matrix.ends) univ ((C.chart g r).symm x).1 v=
      directedEnergy C.matrix.ends v ((C.matrix.affineChart g r).symm x).1 := by
  rw [graph_energy]
  congr 1

/-- Every nonreference node resonance is its exact finite integer phase matrix. -/
theorem nodeResonance_matrix {d : ℕ} (g r : Mom d) (x : Fin C.shape.n → Mom d)
    (i : Fin C.shape.n) (hi : i ≠ C.shape.x0) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r i=
      quadraticEval (C.matrix.phaseMatrix (C.atom i).1) (attachGap x r) := by
  change energy (graphMolecule C.matrix.ends) univ ((C.chart g r).symm x).1 (C.atom i).1+
    (if i=C.shape.x0 then ‖g‖^2-‖g-r‖^2 else 0)=_
  rw [ite_eq_right hi,add_zero,C.chart_energy]
  exact C.matrix.affineChart_energy_interior g r x (C.atom i).1 (C.atom_interior i hi).1 (C.atom_interior i hi).2

end WaveTurbulence.Vine.Param.NormalizedVineCertificate
