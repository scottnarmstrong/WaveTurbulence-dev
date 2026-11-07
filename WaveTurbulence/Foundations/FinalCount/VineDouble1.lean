/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess5
public import WaveTurbulence.Foundations.FinalCount.TriLattice
public import WaveTurbulence.Foundations.FinalCount.AlphaCount
/-! The label count of a VC formed by two double bonds, part 1 (FINALCOUNT-G2; DH23 L1801 last sentence):
the shape `a = x = b` and the conservation at the middle atom `x`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **A VC formed by two double bonds** `a = x = b` (Prop `subsetvc`; three atoms, the joints `a, b` have degree `2`
in the VC, namely the darts `x₁, x₂` resp. `y₁, y₂`, and the middle atom `x` has the four mates of these darts). -/
structure DoubleShape {M : Molecule V D} (K : VineCut M) where
  x : V
  x_mem : x ∈ M.atoms
  x_ne_a : x ≠ K.C.upper
  x_ne_b : x ≠ K.C.lower
  atoms_eq : K.C.atoms = {K.C.upper, x, K.C.lower}
  darts_x : M.dartsAt x = {M.mate K.x₁, M.mate K.x₂, M.mate K.y₁, M.mate K.y₂}

theorem mate_inj' (M : Molecule V D) {a b : D} (h : M.mate a = M.mate b) : a = b := by
  rw [← M.mate_mate a, h, M.mate_mate]

namespace VineCut
variable {M : Molecule V D} (K : VineCut M)

theorem Mx₁ : M.atom K.x₁ = K.C.upper := K.cut_a.2.2.1
theorem Mx₂ : M.atom K.x₂ = K.C.upper := K.cut_a.2.2.2.1
theorem Mout₁ : M.out K.x₁ = false := K.cut_a.2.2.2.2.2.1
theorem Mout₂ : M.out K.x₂ = true := K.cut_a.2.2.2.2.2.2

theorem My₁ : M.atom K.y₁ = K.C.lower := by
  have h : K.m1.atom K.y₁ = K.C.lower := K.cut_b.2.2.1
  change (M.cut K.C.upper K.fa K.x₁ K.x₂).atom K.y₁ = _ at h
  rw [cut_atom] at h
  split_ifs at h with hh
  · exact absurd h K.fa_ne_b
  · exact h

theorem My₂ : M.atom K.y₂ = K.C.lower := by
  have h : K.m1.atom K.y₂ = K.C.lower := K.cut_b.2.2.2.1
  change (M.cut K.C.upper K.fa K.x₁ K.x₂).atom K.y₂ = _ at h
  rw [cut_atom] at h
  split_ifs at h with hh
  · exact absurd h K.fa_ne_b
  · exact h

theorem Mouty₁ : M.out K.y₁ = false := K.cut_b.2.2.2.2.2.1
theorem Mouty₂ : M.out K.y₂ = true := K.cut_b.2.2.2.2.2.2

theorem x₁_ne_x₂ : K.x₁ ≠ K.x₂ := cut_x_ne M K.cut_a
theorem y₁_ne_y₂ : K.y₁ ≠ K.y₂ := cut_x_ne K.m1 K.cut_b
theorem x_ne_y (p q : D) (hp : M.atom p = K.C.upper) (hq : M.atom q = K.C.lower) : p ≠ q := fun e =>
  K.ab_ne (hp.symm.trans ((congrArg M.atom e).trans hq))

end VineCut

namespace DoubleShape
variable {M : Molecule V D} {K : VineCut M} (S : DoubleShape K)

theorem sum_x {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ z ∈ M.dartsAt S.x, g z = g (M.mate K.x₁) + g (M.mate K.x₂) + g (M.mate K.y₁) + g (M.mate K.y₂) := by
  rw [S.darts_x]
  have h12 : M.mate K.x₁ ≠ M.mate K.x₂ := fun e => K.x₁_ne_x₂ (mate_inj' M e)
  have h13 : M.mate K.x₁ ≠ M.mate K.y₁ := fun e => K.x_ne_y _ _ K.Mx₁ K.My₁ (mate_inj' M e)
  have h14 : M.mate K.x₁ ≠ M.mate K.y₂ := fun e => K.x_ne_y _ _ K.Mx₁ K.My₂ (mate_inj' M e)
  have h23 : M.mate K.x₂ ≠ M.mate K.y₁ := fun e => K.x_ne_y _ _ K.Mx₂ K.My₁ (mate_inj' M e)
  have h24 : M.mate K.x₂ ≠ M.mate K.y₂ := fun e => K.x_ne_y _ _ K.Mx₂ K.My₂ (mate_inj' M e)
  have h34 : M.mate K.y₁ ≠ M.mate K.y₂ := fun e => K.y₁_ne_y₂ (mate_inj' M e)
  rw [Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_pair h34]
  abel

theorem deg_x : M.deg S.x = 4 := by
  unfold Molecule.deg
  rw [S.darts_x]
  have h12 : M.mate K.x₁ ≠ M.mate K.x₂ := fun e => K.x₁_ne_x₂ (mate_inj' M e)
  have h13 : M.mate K.x₁ ≠ M.mate K.y₁ := fun e => K.x_ne_y _ _ K.Mx₁ K.My₁ (mate_inj' M e)
  have h14 : M.mate K.x₁ ≠ M.mate K.y₂ := fun e => K.x_ne_y _ _ K.Mx₁ K.My₂ (mate_inj' M e)
  have h23 : M.mate K.x₂ ≠ M.mate K.y₁ := fun e => K.x_ne_y _ _ K.Mx₂ K.My₁ (mate_inj' M e)
  have h24 : M.mate K.x₂ ≠ M.mate K.y₂ := fun e => K.x_ne_y _ _ K.Mx₂ K.My₂ (mate_inj' M e)
  have h34 : M.mate K.y₁ ≠ M.mate K.y₂ := fun e => K.y₁_ne_y₂ (mate_inj' M e)
  rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]), Finset.card_insert_of_notMem (by simp [h23, h24]),
    Finset.card_pair h34]

theorem sign_m₁ : M.dartSign (M.mate K.x₁) = 1 := by
  simp [Molecule.dartSign, M.out_mate, K.Mout₁]
theorem sign_m₂ : M.dartSign (M.mate K.x₂) = -1 := by
  simp [Molecule.dartSign, M.out_mate, K.Mout₂]
theorem sign_m₃ : M.dartSign (M.mate K.y₁) = 1 := by
  simp [Molecule.dartSign, M.out_mate, K.Mouty₁]
theorem sign_m₄ : M.dartSign (M.mate K.y₂) = -1 := by
  simp [Molecule.dartSign, M.out_mate, K.Mouty₂]

end DoubleShape
end WaveTurbulence.FinalCount
