/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapFrontJoints
public import WaveTurbulence.Foundations.Molecule.VineFourDoublePair
public import WaveTurbulence.Foundations.Molecule.VineEraseAdjacency
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
import Mathlib.Tactic

/-! # Both positive-cap joints branch after deletion of their designated added bond -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

omit [Fintype D] [DecidableEq D] in
/-- Each front predecessor is selected and differs from the opposite
front atom; these are the two surviving neighbors at the adjoint joints. -/
theorem front_predecessors (hr : 1 ≤ r) :
    C.side.ladder.u (r-1) ∈ A ∧ C.side.ladder.v (r-1) ∈ A ∧
      C.side.ladder.v r ≠ C.side.ladder.u (r-1) ∧
      C.side.ladder.u r ≠ C.side.ladder.v (r-1) := by
  by_cases hr1 : r=1
  · have he : r-1=0 := by omega
    rw [he,C.side.start_upper,C.side.start_lower]
    have hul := C.label_upper r hr le_rfl
    have hvl := C.label_lower r hr le_rfl
    refine ⟨C.triangle_mem.2.1,C.triangle_mem.2.2,?_,?_⟩
    · intro hh
      have heq := congrArg C.label hh
      rw [hvl,C.label_triangle.2.1] at heq
      omega
    · intro hh
      have heq := congrArg C.label hh
      rw [hul,C.label_triangle.2.2] at heq
      omega
  · have hp : 1 ≤ r-1 := by omega
    have hpn : r-1 ≤ n+1 := by have := C.r_le; omega
    have hum := (C.upper_mem_iff (r-1) hp hpn).mpr (by omega)
    have hvm := (C.lower_mem_iff (r-1) hp hpn).mpr (by omega)
    refine ⟨hum,hvm,?_,?_⟩
    · exact (C.side.ladder.upper_ne_lower hp (by have := C.r_le; omega) hr C.r_le).symm
    · exact C.side.ladder.upper_ne_lower hr C.r_le hp (by have := C.r_le; omega)

/-- A designated hyper-block adjoint keeps one doubled-rung copy and the
predecessor rail at each positive-cap joint, hence two distinct neighbors. -/
theorem erased_front_branches (hM : M.IsMolecule) {x y : V}
    (hH : Mole.IsHyperBlock M A x y) (e : D) (he : M.ends e=s(x,y)) (hr : 1 ≤ r) :
    (∃ u v,(Mole.induced (Mole.eraseBond M e) A).Adj (C.side.ladder.u r) u ∧
      (Mole.induced (Mole.eraseBond M e) A).Adj (C.side.ladder.u r) v ∧ u ≠ v) ∧
    (∃ u v,(Mole.induced (Mole.eraseBond M e) A).Adj (C.side.ladder.v r) u ∧
      (Mole.induced (Mole.eraseBond M e) A).Adj (C.side.ladder.v r) v ∧ u ≠ v) := by
  have hp := C.hyper_front_joints_pos hM hH hr
  have hne := C.side.ladder.upper_ne_lower hr C.r_le hr C.r_le
  have hs := sym2_eq_of_finset_pair_eq hne hp
  have hefront : M.ends e=s(C.side.ladder.u r,C.side.ladder.v r) := he.trans hs.symm
  have hdouble := eraseBond_double_pair_adj M e (C.side.ladder.upper r hr C.r_le).doublePair hne hefront
  obtain ⟨hpu,hpv,hvu,huv⟩ := C.front_predecessors hr
  have hru : C.side.ladder.u r ∈ A := (C.upper_mem_iff r hr (by have := C.r_le; omega)).mpr le_rfl
  have hrv : C.side.ladder.v r ∈ A := (C.lower_mem_iff r hr (by have := C.r_le; omega)).mpr le_rfl
  have hrailU : (Mole.eraseBond M e).Adj (C.side.ladder.u r) (C.side.ladder.u (r-1)) := by
    apply eraseBond_adj_of_pair_ne M e (C.side.ladder.upper_prev_adj r hr C.r_le)
    rw [hefront]
    exact sym2_pair_ne_of_right_ne _ hvu.symm
  have hrailV : (Mole.eraseBond M e).Adj (C.side.ladder.v r) (C.side.ladder.v (r-1)) := by
    apply eraseBond_adj_of_pair_ne M e (C.side.ladder.lower_prev_adj r hr C.r_le)
    rw [hefront,Sym2.eq_swap (a:=C.side.ladder.u r) (b:=C.side.ladder.v r)]
    exact sym2_pair_ne_of_right_ne _ huv.symm
  constructor
  · exact ⟨C.side.ladder.v r,C.side.ladder.u (r-1),
      (Mole.induced_adj_iff _ _ _ _).mpr ⟨hdouble,hru,hrv⟩,
      (Mole.induced_adj_iff _ _ _ _).mpr ⟨hrailU,hru,hpu⟩,hvu⟩
  · exact ⟨C.side.ladder.u r,C.side.ladder.v (r-1),
      (Mole.induced_adj_iff _ _ _ _).mpr ⟨Mole.adj_symmetric _ hdouble,hrv,hru⟩,
      (Mole.induced_adj_iff _ _ _ _).mpr ⟨hrailV,hrv,hpv⟩,huv⟩

end CapPrefixData
end WaveTurbulence.Vine
