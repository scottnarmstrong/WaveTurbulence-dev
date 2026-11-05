/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences

/-!
# Positional tools for actual rung incidences

TARGET molecpl (2): the rung adjacent to either vine joint is available,
including the sole rung when m=1. Endpoint reversal only reorders the two
rail incidences and preserves the actual half-edge witnesses.
-/

public section
namespace WaveTurbulence.Molecpl
open Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reversing the rail direction retains both doubled incidences unchanged. -/
@[expose] def FourIncidences.swapRails {M : Molecule V D} {c d a b : V}
    (R : Vine.FourIncidences M c ![d,d,a,b]) : Vine.FourIncidences M c ![d,d,b,a] where
  dart := R.dart ∘ Equiv.swap (2:Fin 4) 3
  injective := R.injective.comp (Equiv.swap (2:Fin 4) 3).injective
  atom_eq := fun i => R.atom_eq _
  neighbor_eq := by
    intro i
    fin_cases i
    · exact R.neighbor_eq 0
    · exact R.neighbor_eq 1
    · exact R.neighbor_eq 3
    · exact R.neighbor_eq 2

/-- The two atoms of every actual rung are distinct, also at the one-rung endpoint. -/
theorem fullRungSequence_rung_ne {M : Molecule V D} {n : ℕ} (Q : FullRungSequence M n)
    {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) : Q.u i ≠ Q.v i := by
  intro he
  let j : Fin n := ⟨i-1,by omega⟩
  have hj : j.1+1=i := by dsimp [j]; omega
  have hh : (Sum.inl j : Fin n ⊕ Fin n) = Sum.inr j :=
    Q.distinct (by simpa only [Sum.elim_inl,Sum.elim_inr,hj] using he)
  cases hh

/-- Distinct internal rung indices have disjoint pairs of atoms. -/
theorem fullRungSequence_pair_disjoint {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : 1 ≤ j) (hjn : j ≤ n) (hne : i ≠ j) :
    Q.u i ≠ Q.u j ∧ Q.u i ≠ Q.v j ∧ Q.v i ≠ Q.u j ∧ Q.v i ≠ Q.v j := by
  let ii : Fin n := ⟨i-1,by omega⟩
  let jj : Fin n := ⟨j-1,by omega⟩
  have hii : ii.1+1=i := by dsimp [ii]; omega
  have hjj : jj.1+1=j := by dsimp [jj]; omega
  have hd : ii ≠ jj := by
    intro he
    have hh := congrArg Fin.val he
    dsimp [ii,jj] at hh
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    have hh : (Sum.inl ii : Fin n ⊕ Fin n) = Sum.inl jj :=
      Q.distinct (by simpa only [Sum.elim_inl,hii,hjj] using he)
    exact hd (Sum.inl.inj hh)
  · intro he
    have hh : (Sum.inl ii : Fin n ⊕ Fin n) = Sum.inr jj :=
      Q.distinct (by simpa only [Sum.elim_inl,Sum.elim_inr,hii,hjj] using he)
    cases hh
  · intro he
    have hh : (Sum.inr ii : Fin n ⊕ Fin n) = Sum.inl jj :=
      Q.distinct (by simpa only [Sum.elim_inl,Sum.elim_inr,hii,hjj] using he)
    cases hh
  · intro he
    have hh : (Sum.inr ii : Fin n ⊕ Fin n) = Sum.inr jj :=
      Q.distinct (by simpa only [Sum.elim_inr,hii,hjj] using he)
    exact hd (Sum.inr.inj hh)

/-- Four incidences whose neighbors all lie in S force internal degree four. -/
theorem fourIncidences_internal_degree {M : Molecule V D} (hM : M.IsMolecule)
    {S : Finset V} {c : V} {vs : Fin 4 → V} (R : FourIncidences M c vs)
    (hc : c ∈ S) (hv : ∀ i, vs i ∈ S) : M.degIn S c = 4 := by
  rw [Vine.fourIncidences_degree M hM R S hc]
  have he (i : Fin 4) : Vine.jointIndicator S (vs i) = 1 := ite_eq_left (hv i)
  simp_rw [he]
  norm_num

end WaveTurbulence.Molecpl
