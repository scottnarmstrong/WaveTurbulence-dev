/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality
import Mathlib.Tactic.Ring

/-!
# Diagonalization of the quadratic phases in the standard Weyl reductions

The bilinear change of variables has a parity constraint on the integer
lattice. The three-variable phase in TARGET (lemcub3) has the analogous
constraint on all three transformed coordinates. The identities are exact,
so arbitrary shifted linear frequencies may be included before tensorization.
-/

public section
namespace WaveTurbulence.WeylSums

/-- The exact image lattice of the bilinear diagonalization. -/
theorem exists_bilinear_integer_coordinates (p q : ℤ) :
    (∃ x y : ℤ, p = x+y ∧ q = x-y) ↔ Even (p-q) := by
  constructor
  · rintro ⟨x,y,rfl,rfl⟩
    exact ⟨y, by ring⟩
  · rintro ⟨k,hk⟩
    exact ⟨q+k,k, by linarith, by ring⟩

/-- The exact image lattice for the three-variable diagonalization. -/
theorem exists_cubic_integer_coordinates (u v w : ℤ) :
    (∃ x y z : ℤ, u=x+y ∧ v=x-y ∧ w=x+y-2*z) ↔
      Even (u-v) ∧ Even (u-w) := by
  constructor
  · rintro ⟨x,y,z,rfl,rfl,rfl⟩
    exact ⟨⟨y, by ring⟩, ⟨z, by ring⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨v+a,a,b, by linarith, by ring, by linarith⟩

/-- The bilinear change of variables is a bijection onto its parity lattice. -/
@[expose] noncomputable def bilinearLatticeEquiv :
    (ℤ × ℤ) ≃ {pq : ℤ × ℤ // Even (pq.1-pq.2)} :=
  Equiv.ofBijective (fun xy => ⟨(xy.1+xy.2, xy.1-xy.2), ⟨xy.2, by ring⟩⟩)
    ⟨by
      intro x y h
      have hp := congrArg (fun z => z.val.1) h
      have hq := congrArg (fun z => z.val.2) h
      apply Prod.ext <;> dsimp at hp hq ⊢ <;> linarith,
     by
      rintro ⟨⟨p,q⟩,hpq⟩
      obtain ⟨x,y,hp,hq⟩ := (exists_bilinear_integer_coordinates p q).mpr hpq
      refine ⟨(x,y), Subtype.ext ?_⟩
      exact Prod.ext hp.symm hq.symm⟩

/-- The cubic change of variables is a bijection onto its parity lattice. -/
@[expose] noncomputable def cubicLatticeEquiv :
    (ℤ × ℤ × ℤ) ≃ {uvw : ℤ × ℤ × ℤ // Even (uvw.1-uvw.2.1) ∧ Even (uvw.1-uvw.2.2)} :=
  Equiv.ofBijective
    (fun xyz => ⟨(xyz.1+xyz.2.1, xyz.1-xyz.2.1, xyz.1+xyz.2.1-2*xyz.2.2),
      ⟨⟨xyz.2.1, by ring⟩, ⟨xyz.2.2, by ring⟩⟩⟩)
    ⟨by
      intro x y h
      have hu := congrArg (fun z => z.val.1) h
      have hv := congrArg (fun z => z.val.2.1) h
      have hw := congrArg (fun z => z.val.2.2) h
      apply Prod.ext
      · dsimp at hu hv hw ⊢; linarith
      · apply Prod.ext <;> dsimp at hu hv hw ⊢ <;> linarith,
     by
      rintro ⟨⟨u,v,w⟩,huvw⟩
      obtain ⟨x,y,z,hu,hv,hw⟩ := (exists_cubic_integer_coordinates u v w).mpr huvw
      refine ⟨(x,y,z), Subtype.ext ?_⟩
      exact Prod.ext hu.symm (Prod.ext hv.symm hw.symm)⟩

/-- Exact reindexing of the bilinear lattice sum, including its parity constraint. -/
theorem tsum_bilinear_lattice (F : ℤ → ℤ → ℂ) :
    (∑' xy : ℤ × ℤ, F (xy.1+xy.2) (xy.1-xy.2)) =
      ∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, F pq.val.1 pq.val.2 :=
  bilinearLatticeEquiv.tsum_eq (fun pq => F pq.val.1 pq.val.2)

/-- Exact reindexing of the cubic lattice sum, including both parity constraints. -/
theorem tsum_cubic_lattice (F : ℤ → ℤ → ℤ → ℂ) :
    (∑' xyz : ℤ × ℤ × ℤ, F (xyz.1+xyz.2.1) (xyz.1-xyz.2.1)
      (xyz.1+xyz.2.1-2*xyz.2.2)) =
      ∑' uvw : {uvw : ℤ × ℤ × ℤ // Even (uvw.1-uvw.2.1) ∧ Even (uvw.1-uvw.2.2)},
        F uvw.val.1 uvw.val.2.1 uvw.val.2.2 :=
  cubicLatticeEquiv.tsum_eq (fun uvw => F uvw.val.1 uvw.val.2.1 uvw.val.2.2)

/-- Character formula retaining the parity sublattice exactly. -/
theorem parity_indicator (k : ℤ) :
    (if Even k then (1 : ℂ) else 0) = (1 + (-1 : ℂ)^k) / 2 := by
  by_cases hk : Even k
  · simp [hk, hk.neg_one_zpow]
  · have ho : Odd k := Int.not_even_iff_odd.mp hk
    simp [hk, ho.neg_one_zpow]

/-- Half-integral linear phases encode the parity constraint. -/
theorem e_half_int (k : ℤ) : e ((k : ℝ) / 2) = (-1 : ℂ)^k := by
  unfold e
  rw [show ((2 * Real.pi * ((k : ℝ) / 2) : ℝ) : ℂ) * Complex.I =
    (k : ℂ) * (Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Removing a parity constraint produces two shifted linear frequencies.
Two such constraints produce the four terms in the cubic reduction. -/
theorem parity_phase (k : ℤ) (φ : ℝ) :
    (if Even k then (1 : ℂ) else 0) * e φ =
      (e φ + e (φ + (k : ℝ)/2)) / 2 := by
  rw [parity_indicator, e_add, e_half_int]
  ring

end WaveTurbulence.WeylSums
