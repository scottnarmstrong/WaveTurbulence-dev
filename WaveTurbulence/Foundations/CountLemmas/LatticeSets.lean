/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-! # The lattice sets in TARGET Lemmas A.8 and A.9 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- The exact unit-ball predicate in the audited B1 counting drafts. -/
@[expose] def NearLattice {d : ℕ} (L : ℝ) (a : Mom d) (n : Fin d → ℤ) : Prop :=
  ‖latticePoint L n - a‖ ≤ 1

/-- The two-vector set, retaining the integer unit sign from B1.8. -/
@[expose] def atomPairSet {d : ℕ} (L : ℝ) (a b : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L a q.1 ∧ NearLattice L b q.2 ∧ q.1 + (ε : ℤ) • q.2 = nk ∧
    |‖latticePoint L q.1‖ ^ 2 + (ε : ℤ) * ‖latticePoint L q.2‖ ^ 2 - β| ≤ τ}

/-- The three-vector set in B1.8, with the draft's order of conjuncts. -/
@[expose] def atomTripleSet {d : ℕ} (L : ℝ) (a b c : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) :
    Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L a q.1 ∧ NearLattice L b q.2.1 ∧ NearLattice L c q.2.2 ∧
    q.1 - q.2.1 + q.2.2 = nk ∧
    |‖latticePoint L q.1‖ ^ 2 - ‖latticePoint L q.2.1‖ ^ 2 +
      ‖latticePoint L q.2.2‖ ^ 2 - β| ≤ τ}

/-- Unit balls lie in translated integer boxes after multiplication by `L`. -/
theorem nearLattice_mem_box {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a : Mom d) (n : Fin d → ℤ) (hn : NearLattice L a n) :
    n ∈ Counting.latticeBox (fun i => L * a i) L := by
  apply (Counting.mem_latticeBox _ _ _).mpr
  intro i
  have hi : |(n i : ℝ) / L - a i| ≤ 1 :=
    (show |(latticePoint L n - a) i| ≤ ‖latticePoint L n - a‖ from
      by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n-a) i).trans hn
  have he : (n i : ℝ) - L * a i = L * ((n i : ℝ) / L - a i) := by
    field_simp
  rw [he,abs_mul,abs_of_pos hL]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hL.le

/-- Finiteness is explicit, so subsequent `ncard` bounds cannot use junk values. -/
theorem finite_nearLattice {d : ℕ} {L : ℝ} (hL : 0 < L) (a : Mom d) :
    {n | NearLattice L a n}.Finite :=
  (Counting.latticeBox (fun i => L*a i) L).finite_toSet.subset
    (fun n hn => nearLattice_mem_box hL a n hn)

theorem finite_atomPairSet {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a b : Mom d) (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) :
    (atomPairSet L a b nk β τ ε).Finite :=
  ((finite_nearLattice hL a).prod (finite_nearLattice hL b)).subset
    (fun _ h => ⟨h.1,h.2.1⟩)

theorem finite_atomTripleSet {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a b c : Mom d) (nk : Fin d → ℤ) (β τ : ℝ) :
    (atomTripleSet L a b c nk β τ).Finite :=
  ((finite_nearLattice hL a).prod
    ((finite_nearLattice hL b).prod (finite_nearLattice hL c))).subset
    (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩)

end WaveTurbulence.CountLemmas
