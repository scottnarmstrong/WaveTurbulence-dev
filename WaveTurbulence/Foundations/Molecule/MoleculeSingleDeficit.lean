/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # A single unsaturated atom has internal degree two -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- If every other atom of an atomic group has internal degree four, its
remaining positive joint has degree two: saturation excludes degree four,
and handshaking excludes degree three. -/
theorem single_deficit_degree_two (hM : M.IsMolecule) {S : Finset V} {c : V}
    (hS : S ⊆ M.atoms) (hc : c ∈ S) (hmin : 2 ≤ M.degIn S c)
    (hfull : ∀ z ∈ S, z ≠ c → M.degIn S z = 4) : M.degIn S c = 2 := by
  have hle := (degIn_le_deg M S c).trans (deg_le_four M hM (hS hc))
  have hne4 : M.degIn S c ≠ 4 := by
    intro h4
    apply no_saturated_group M hM hS ⟨c,hc⟩
    intro z hz
    by_cases hzc : z = c
    · exact hzc.symm ▸ h4
    · exact hfull z hz hzc
  have hs4 : ∑ z ∈ S.erase c, M.degIn S z = 4*(S.erase c).card := by
    calc
      _ = ∑ _z ∈ S.erase c, (4:ℕ) := by
        apply Finset.sum_congr rfl
        intro z hz
        obtain ⟨hn,hzS⟩ := Finset.mem_erase.mp hz
        exact hfull z hzS hn
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
  have hsum := Finset.add_sum_erase S (fun z => M.degIn S z) hc
  rw [hs4,sum_degreesIn_eq_two_mul_groupBonds] at hsum
  omega

/-- Equal incidence counts along a group inclusion give equality of the
actual internal dart sets at that atom. -/
theorem internal_darts_eq_of_degree_eq {A B : Finset V} (hAB : A ⊆ B) (v : V)
    (hd : M.degIn A v = M.degIn B v) :
    (M.dartsAt v).filter (M.InGroup A) = (M.dartsAt v).filter (M.InGroup B) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨hxv,hxa,hxm⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxv,hAB hxa,hAB hxm⟩
  · exact hd.ge

end WaveTurbulence.Mole
