/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
import Mathlib.Tactic

/-! # Orientation identities at the two ends of an actual boundary bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_incidence_sign_opposite_from (M : Molecule V D) (a b : V) (x y : D) :
    appbIncidenceSign M a x ≠ appbIncidenceSign M b y ↔ AppbOppositeFrom M a b x y := by
  by_cases hx : M.atom x = a <;> by_cases hy : M.atom y = b
  all_goals simp [appbIncidenceSign,AppbOppositeFrom,hx,hy]

theorem appb_incidence_sign_endpoints (M : Molecule V D) (x : D) (a b : V)
    (he : M.ends x = s(a,b)) (hne : a ≠ b) :
    appbIncidenceSign M a x = -appbIncidenceSign M b x := by
  rcases Sym2.eq_iff.mp he with h | h
  all_goals simp [appbIncidenceSign,h.1,h.2,hne,hne.symm]

theorem appb_d33_external_signs_opposite {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (ho : AppbD33BoundaryOpposite M r) :
    appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val ≠
      appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val := by
  have h13 : r.vertex 1 ≠ r.vertex 3 := (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  have h24 : r.vertex 2 ≠ r.vertex 4 := (r.vertex_eq_iff 2 4 (by decide) (by decide)).not.mpr (by decide)
  have hs2 := appb_incidence_sign_endpoints M _ _ _ (r.endpoints ⟨2,by decide⟩) h13
  have hs3 := appb_incidence_sign_endpoints M _ _ _ (r.endpoints ⟨3,by decide⟩) h24
  have hi := (appb_incidence_sign_opposite_from M (r.vertex 1) (r.vertex 2) _ _).mpr ho
  change appbIncidenceSign M (r.vertex 1) (r.edge ⟨2,by decide⟩).val =
    -appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val at hs2
  change appbIncidenceSign M (r.vertex 2) (r.edge ⟨3,by decide⟩).val =
    -appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val at hs3
  intro h
  apply hi
  rw [hs2,hs3,h]

end WaveTurbulence.Mole
