/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExtendSequence
public import WaveTurbulence.Foundations.Molecule.VineAssembleIncidences
import Mathlib.Tactic

/-! # Extending rung sequences using actual doubled edges and port rails -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- Distinct complete rails never share an atom, including their old endpoints. -/
theorem full_rails_cross {M : Molecule V D} {n : ℕ} (Q : FullRungSequence M n)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => Q.u i.1)
      (fun i : Fin (n+2) => Q.v i.1))) (i j : Fin (n+2)) : Q.u i.1 ≠ Q.v j.1 := by
  intro he
  have hh : (Sum.inl i : Fin (n+2) ⊕ Fin (n+2))=Sum.inr j := hd he
  cases hh

/-- Actual double pairs and four boundary rail edges produce the enlarged
full-rung sequence. The external-neighbor inequalities only ensure that
these four incidence rows use distinct darts. -/
@[expose] noncomputable def FullRungSequence.extendOfEdges {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (p q r s : V)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => Q.u i.1)
      (fun i : Fin (n+2) => Q.v i.1)))
    (R0 : TwoIncidences M (Q.u 0) (Q.v 0))
    (RN : TwoIncidences M (Q.u (n+1)) (Q.v (n+1)))
    (hp : M.Adj (Q.u 0) p) (hq : M.Adj (Q.u (n+1)) q)
    (hr : M.Adj (Q.v 0) r) (hs : M.Adj (Q.v (n+1)) s)
    (hrail : M.Adj (Q.u 0) (Q.u 1) ∧ M.Adj (Q.v 0) (Q.v 1) ∧
      M.Adj (Q.u n) (Q.u (n+1)) ∧ M.Adj (Q.v n) (Q.v (n+1)))
    (hpv : p ≠ Q.v 0) (hpu : p ≠ Q.u 1)
    (hqu : q ≠ Q.u n) (hqv : q ≠ Q.v (n+1))
    (hru : r ≠ Q.u 0) (hrv : r ≠ Q.v 1)
    (hsv : s ≠ Q.v n) (hsu : s ≠ Q.u (n+1)) : FullRungSequence M (n+2) := by
  have hc (i j : ℕ) (hi : i<n+2) (hj : j<n+2) : Q.u i ≠ Q.v j :=
    full_rails_cross Q hd ⟨i,hi⟩ ⟨j,hj⟩
  let hu0 := Classical.choice (fourIncidences_of_double_and_edges R0 hp hrail.1 hpv.symm
    (hc 1 0 (by omega) (by omega)).symm hpu)
  let hv0 := Classical.choice (fourIncidences_of_double_and_edges R0.mates hr hrail.2.1 hru.symm
    (hc 0 1 (by omega) (by omega)) hrv)
  let huN := Classical.choice (fourIncidences_of_double_and_edges RN
    (Mole.adj_symmetric M hrail.2.2.1) hq
    (hc n (n+1) (by omega) (by omega)).symm hqv.symm hqu.symm)
  let hvN := Classical.choice (fourIncidences_of_double_and_edges RN.mates
    (Mole.adj_symmetric M hrail.2.2.2) hs
    (hc (n+1) n (by omega) (by omega)) hsu.symm hsv.symm)
  exact Q.extend p q r s hd hu0 hv0 huN hvN

end WaveTurbulence.Vine
