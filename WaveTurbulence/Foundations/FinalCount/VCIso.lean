/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAdm
/-! # VINE-COUNT part 25: relabelling of darts.

If two molecules on the same atom type are related by a bijection of darts commuting with `atom`, `mate`, `out`
(and with the same atoms), then bond multiplicities, directions, ladders, maximal ladders, ladder gaps and the
number of bonds agree.  Used to compare the removed vine of a hyper object, computed in `M` and in the adjoint
`eraseBond M e`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D1 D2 : Type*} [DecidableEq V] [Fintype D1] [DecidableEq D1] [Fintype D2] [DecidableEq D2] {d : ℕ}
  {N1 : Molecule V D1} {N2 : Molecule V D2} (f : D1 ≃ D2)
  (hat : ∀ x, N2.atom (f x) = N1.atom x) (hm : ∀ x, N2.mate (f x) = f (N1.mate x))
  (ho : ∀ x, N2.out (f x) = N1.out x)

section Iso
include hat hm

theorem iso_ends (x : D1) : N2.ends (f x) = N1.ends x := by
  unfold Molecule.ends; rw [hat, hm, hat]

include ho in
theorem iso_bondsBetween (a b : V) : N2.bondsBetween a b = N1.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  refine (Finset.card_bij (fun x _ => f.symm x) ?_ ?_ ?_)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have e : x = f (f.symm x) := (f.apply_symm_apply x).symm
    rw [e] at h1 h2
    exact ⟨by rw [← ho]; exact h1, by rw [← iso_ends f hat hm]; exact h2⟩
  · intro x _ y _ h
    simpa using h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨f y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [ho]; exact hy.1, by rw [iso_ends f hat hm]; exact hy.2⟩

include ho in
theorem iso_directed (a b : V) : N2.Directed a b ↔ N1.Directed a b := by
  unfold Molecule.Directed
  constructor
  · rintro ⟨x, h1, h2, h3⟩
    refine ⟨f.symm x, ?_, ?_, ?_⟩
    · rw [← ho, f.apply_symm_apply]; exact h1
    · rw [← hat, f.apply_symm_apply]; exact h2
    · have e : N2.mate x = f (N1.mate (f.symm x)) := by
        have := hm (f.symm x); rwa [f.apply_symm_apply] at this
      rw [e, hat] at h3; exact h3
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨f x, by rw [ho]; exact h1, by rw [hat]; exact h2, by rw [hm, hat]; exact h3⟩

include ho in
theorem iso_bonds_card : N2.bonds.card = N1.bonds.card := by
  unfold Molecule.bonds
  refine (Finset.card_bij (fun x _ => f.symm x) ?_ ?_ ?_)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← ho, f.apply_symm_apply]; exact hx
  · intro x _ y _ h; simpa using h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ⟨f y, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [ho]; exact hy, by simp⟩

variable (hA : N1.atoms = N2.atoms)
include ho hA

theorem iso_isLadder {m : ℕ} (u v : Fin (m + 1) → V) : N2.IsLadder u v ↔ N1.IsLadder u v := by
  unfold Molecule.IsLadder
  simp only [iso_bondsBetween f hat hm ho, iso_directed f hat hm ho, hA]

theorem iso_isLadderSet (S : Finset V) : N2.IsLadderSet S ↔ N1.IsLadderSet S := by
  unfold Molecule.IsLadderSet
  simp only [iso_isLadder f hat hm ho hA]

theorem iso_maximalLadders : N2.maximalLadders = N1.maximalLadders := by
  classical
  unfold Molecule.maximalLadders
  simp only [iso_isLadderSet f hat hm ho hA, hA]

theorem iso_ladderGap {m : ℕ} (u v : Fin (m + 1) → V) (hm1 : 1 ≤ m) (L : ℝ) (w : Mom d)
    (κ1 : D1 → (Fin d → ℤ)) (κ2 : D2 → (Fin d → ℤ)) (hκ : ∀ x, κ2 (f x) = κ1 x) (r : Mom d) :
    N2.IsLadderGap L w κ2 u v hm1 r ↔ N1.IsLadderGap L w κ1 u v hm1 r := by
  unfold Molecule.IsLadderGap
  constructor
  · rintro ⟨x, y, h1, h2, h3, h4, h5⟩
    refine ⟨f.symm x, f.symm y, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← iso_ends f hat hm, f.apply_symm_apply]; exact h1
    · rw [← iso_ends f hat hm, f.apply_symm_apply]; exact h2
    · rw [← hat, f.apply_symm_apply]; exact h3
    · rw [← hat, f.apply_symm_apply]; exact h4
    · rw [h5]; unfold Molecule.gapAt Molecule.kvec
      rw [← hκ (f.symm x), ← hκ (f.symm y), f.apply_symm_apply, f.apply_symm_apply]
  · rintro ⟨x, y, h1, h2, h3, h4, h5⟩
    refine ⟨f x, f y, ?_, ?_, ?_, ?_, ?_⟩
    · rw [iso_ends f hat hm]; exact h1
    · rw [iso_ends f hat hm]; exact h2
    · rw [hat]; exact h3
    · rw [hat]; exact h4
    · rw [h5]; unfold Molecule.gapAt Molecule.kvec
      rw [hκ x, hκ y]


end Iso

end WaveTurbulence.VineCount
