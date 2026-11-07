/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
public import WaveTurbulence.Foundations.FinalCount.AppBRemovedOutgoingSums
import Mathlib.Tactic

/-! # Orientation balance at an actual degree-four molecule atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def edgeSign (M : Molecule V D) (a : V) (x : D) : ℝ :=
  if M.atom x = a then 1 else -1

theorem edgeSign_sum_zero_iff (M : Molecule V D) (a b : V) (x y : D) :
    edgeSign M a x+edgeSign M b y = 0 ↔ AppbOppositeFrom M a b x y := by
  by_cases hx : M.atom x = a <;> by_cases hy : M.atom y = b
  all_goals simp [edgeSign,AppbOppositeFrom,hx,hy]

theorem edgeSign_endpoints (M : Molecule V D) (x : D) {a b : V}
    (he : M.ends x = s(a,b)) (hne : a ≠ b) : edgeSign M a x = -edgeSign M b x := by
  rcases Sym2.eq_iff.mp he with he | he
  all_goals simp [edgeSign,he.1,he.2,hne,hne.symm]

theorem sum_dartSign_eq_outdeg_sub_indeg (M : Molecule V D) (a : V) :
    (∑ x ∈ M.dartsAt a,M.dartSign x) = (M.outdeg a : ℝ)-M.indeg a := by
  unfold Molecule.dartSign
  rw [sum_ite]
  simp [Molecule.outdeg,Molecule.indeg,Bool.not_eq_true,sub_eq_add_neg]

theorem sum_dartSign_zero_of_degree_four (M : Molecule V D) (hM : M.IsMolecule)
    {a : V} (ha : a ∈ M.atoms) (hd : M.deg a = 4) : (∑ x ∈ M.dartsAt a,M.dartSign x) = 0 := by
  have hs := outdeg_add_indeg M a
  have ho := (hM.1 a ha).1
  have hi := (hM.1 a ha).2
  have ho2 : M.outdeg a = 2 := by omega
  have hi2 : M.indeg a = 2 := by omega
  rw [sum_dartSign_eq_outdeg_sub_indeg,ho2,hi2]
  norm_num

theorem signed_incidence_zero (M : Molecule V D) (a : V) (x : D)
    (h : appbIncidence M a x = 0) :
    ((if M.atom x = a then M.dartSign x else 0)-(if M.atom (M.mate x) = a then M.dartSign x else 0)) = 0 := by
  by_cases hx : M.atom x = a <;> by_cases hy : M.atom (M.mate x) = a
  all_goals simp only [appbIncidence,hx,hy,ite_true,ite_false] at h
  all_goals simp_all

theorem signed_incidence_one (M : Molecule V D) (a : V) (x : D)
    (ho : M.out x = true) (h : appbIncidence M a x = 1) :
    ((if M.atom x = a then M.dartSign x else 0)-(if M.atom (M.mate x) = a then M.dartSign x else 0)) =
      edgeSign M a x := by
  by_cases hx : M.atom x = a <;> by_cases hy : M.atom (M.mate x) = a
  all_goals simp only [appbIncidence,hx,hy,ite_true,ite_false] at h
  all_goals simp_all [Molecule.dartSign,edgeSign]

end WaveTurbulence.Mole.AppbAlgorithm
