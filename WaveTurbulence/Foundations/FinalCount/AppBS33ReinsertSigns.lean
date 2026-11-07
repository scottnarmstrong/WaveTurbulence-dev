/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
public import WaveTurbulence.Foundations.FinalCount.AppBS33TopologySigns
import Mathlib.Tactic

/-! # The two external signs of the 35 reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_external_signs_opposite {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (ho : AppbOppositeFrom M (r.vertex 1) (r.vertex 2) (r.edge ⟨1,by decide⟩).val (r.edge ⟨3,by decide⟩).val) :
    appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val ≠
      appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val := by
  have h13 : r.vertex 1 ≠ r.vertex 3 := (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  have h24 : r.vertex 2 ≠ r.vertex 5 := (r.vertex_eq_iff 2 5 (by decide) (by decide)).not.mpr (by decide)
  have hs2 := appb_incidence_sign_endpoints M _ _ _ (r.endpoints ⟨1,by decide⟩) h13
  have hs3 := appb_incidence_sign_endpoints M _ _ _ (r.endpoints ⟨3,by decide⟩) h24
  have hi := (appb_incidence_sign_opposite_from M (r.vertex 1) (r.vertex 2) _ _).mpr ho
  change appbIncidenceSign M (r.vertex 1) (r.edge ⟨1,by decide⟩).val =
    -appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val at hs2
  change appbIncidenceSign M (r.vertex 2) (r.edge ⟨3,by decide⟩).val =
    -appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val at hs3
  intro h
  apply hi
  rw [hs2,hs3,h]


end WaveTurbulence.Mole
