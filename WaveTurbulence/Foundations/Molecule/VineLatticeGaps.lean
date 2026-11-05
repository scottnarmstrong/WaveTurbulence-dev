/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGapConservation
import Mathlib.Tactic

/-! # Gap conservation for exact B2 lattice decorations (TARGET defdiff) -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ}

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- The generic flow gap is exactly the pinned lattice block-gap predicate. -/
theorem isBlockGap_iff_groupGap (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (S : Finset V) (a : V) (r : Mom d) :
    M.IsBlockGap L w κ S a r ↔ IsGroupGap M S (Molecule.kvec L w κ) a r := Iff.rfl

/-- TARGET defdiff: the two joint gaps of a decorated block have the same
norm. The only conservation assumption is the source's zero value at every
degree-four atom. -/
theorem block_gap_norm_eq (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) (L : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ S b r') : ‖r‖=‖r'‖ := by
  have hk (x : D) : Molecule.kvec L w κ (M.mate x)=Molecule.kvec L w κ x := by
    simp only [Molecule.kvec,hκ.1 x]
  have he := block_gaps_neg M hM hB (Molecule.kvec L w κ) hk
    (fun v hv hd => (hκ.2 v hv).trans (hc v hv hd))
    ((isBlockGap_iff_groupGap M L w κ S a r).mp hr)
    ((isBlockGap_iff_groupGap M L w κ S b r').mp hr')
  rw [he,norm_neg]

end WaveTurbulence.Vine
