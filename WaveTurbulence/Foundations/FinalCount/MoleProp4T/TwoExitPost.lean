/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExit
public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
import Mathlib.Tactic

/-! # The (Y2) post molecule of a two-exit set and the transported decoration

DH23 L1954: "we then define a decoration of `𝕄′` ... by assigning `k_{ℓ'} = k_{ℓ₂} + g (k_{ℓ₁} − k_{ℓ₂})` for some
`|g| ≲ 3`". Here `ℓ₁ = x`, `ℓ₂ = y`, the new bond is `d → c`, and `R := ∑_{v ∈ Y} c_v = k_x − k_y` (boundary
identity). The transported labels form a decoration of the post molecule with the fixed charges `c_c − (g−1)R`,
`c_d + gR` (unchanged elsewhere), unchanged energies away from `c, d`, and energies at `c, d` known up to
`(1 + 4|Y|) δ⁻¹L^{-2γ}` (`0 ≤ g ≤ 4`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Star sums of a molecule with one added bond `a → b`. -/
theorem sum_dartsAt_addBond (M : Molecule V D) (a b v : V) {E : Type*} [AddCommMonoid E]
    (F : D ⊕ Bool → E) :
    ∑ z ∈ (Mole.addBond M a b).dartsAt v, F z =
      ∑ z ∈ M.dartsAt v, F (Sum.inl z) + (if a = v then F (Sum.inr true) else 0) +
        (if b = v then F (Sum.inr false) else 0) := by
  unfold Molecule.dartsAt
  rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter, Fintype.sum_bool]
  simp only [Mole.addBond, Sum.elim_inl, Sum.elim_inr, ite_true, Bool.false_eq_true, ite_false]
  rw [add_assoc]
  congr 1

/-- The lattice point of `n₂ + g (n₁ − n₂)`. -/
theorem latticePoint_affine {d : ℕ} (L : ℝ) (n₁ n₂ : Fin d → ℤ) (g : ℤ) :
    latticePoint L (n₂ + g • (n₁ - n₂)) = latticePoint L n₂ + (g : ℝ) • (latticePoint L n₁ - latticePoint L n₂) := by
  ext i
  simp only [latticePoint, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_sub]
  ring

/-- `‖k + r‖² − ‖k + g r‖² = (1−g)(‖k+r‖² − ‖k‖²) + g(1−g)‖r‖²`. -/
theorem norm_sq_shift_c {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k r : E) (g : ℝ) :
    ‖k + r‖ ^ 2 - ‖k + g • r‖ ^ 2 = (1 - g) * (‖k + r‖ ^ 2 - ‖k‖ ^ 2) + g * (1 - g) * ‖r‖ ^ 2 := by
  rw [norm_add_sq_real, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- `‖k + g r‖² − ‖k‖² = g(‖k+r‖² − ‖k‖²) + g(g−1)‖r‖²`. -/
theorem norm_sq_shift_d {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k r : E) (g : ℝ) :
    ‖k + g • r‖ ^ 2 - ‖k‖ ^ 2 = g * (‖k + r‖ ^ 2 - ‖k‖ ^ 2) + g * (g - 1) * ‖r‖ ^ 2 := by
  rw [norm_add_sq_real, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The post molecule**: `Y` and its bonds removed, the new bond `d → c` added. -/
def post : Molecule V (Degen.RetainedDart N T.Y ⊕ Bool) := Mole.addBond (Degen.eraseAtoms N T.Y) T.d T.c

theorem post_atoms : T.post.atoms = N.atoms \ T.Y := by
  change insert T.d (insert T.c (N.atoms \ T.Y)) = _
  rw [insert_eq_of_mem T.c_mem, insert_eq_of_mem T.d_mem]

/-- The transported labels. -/
def postLabels {d : ℕ} (κ : D → (Fin d → ℤ)) (g : ℤ) : Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ) :=
  Sum.elim (fun z => κ z.val) (fun _ => κ T.y + g • (κ T.x - κ T.y))

/-- The fixed exit difference `R = ∑_{v ∈ Y} c_v`. -/
def exitCharge {d : ℕ} (c : V → Mom d) : Mom d := ∑ v ∈ T.Y, c v

/-- The post charges. -/
def postCharges {d : ℕ} (c : V → Mom d) (g : ℤ) (v : V) : Mom d :=
  if v = T.c then c v - ((g : ℝ) - 1) • T.exitCharge c else if v = T.d then c v + (g : ℝ) • T.exitCharge c
  else c v

theorem kvec_x_sub_y {d : ℕ} {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : N.IsDecoration L w c κ) :
    Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y = T.exitCharge c := by
  unfold exitCharge
  rw [sum_charges_eq_cross hκ T.sub, T.cross, sum_pair T.ne]
  unfold Molecule.dartSign
  rw [T.out_x, T.out_y]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_smul, neg_one_smul]
  abel

theorem kvec_postLabels_new {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (g : ℤ) (t : Bool) :
    Molecule.kvec L w (T.postLabels κ g) (Sum.inr t) =
      Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y) := by
  simp only [Molecule.kvec, postLabels, Sum.elim_inr, latticePoint_affine]
  abel

theorem dartSign_mate_x : N.dartSign (N.mate T.x) = -1 := by
  unfold Molecule.dartSign; rw [N.out_mate, T.out_x]; rfl

theorem dartSign_mate_y : N.dartSign (N.mate T.y) = 1 := by
  unfold Molecule.dartSign; rw [N.out_mate, T.out_y]; rfl

theorem post_out_inl (z : Degen.RetainedDart N T.Y) : T.post.out (Sum.inl z) = N.out z.val := rfl

/-- The post star sum of `F` at a surviving atom. -/
theorem post_star_sum {v : V} (hv : v ∉ T.Y) {E : Type*} [AddCommGroup E] (F : D → E) (Fnew : Bool → E) :
    ∑ z ∈ T.post.dartsAt v, Sum.elim (fun z : Degen.RetainedDart N T.Y => F z.val) Fnew z =
      ∑ z ∈ N.dartsAt v, F z - (if v = T.c then F (N.mate T.x) else 0) - (if v = T.d then F (N.mate T.y) else 0) +
        (if T.d = v then Fnew true else 0) + (if T.c = v then Fnew false else 0) := by
  unfold post
  rw [sum_dartsAt_addBond]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hs := Degen.sum_dartsAt_split N T.Y hv F
  rw [T.removedDartsAt_eq hv] at hs
  have hcd := T.c_ne_d
  by_cases hc : v = T.c <;> by_cases hd : v = T.d
  · exact absurd (hc.symm.trans hd) hcd
  · subst hc; simp only [ite_true, show ¬ T.c = T.d from hcd, ite_false, union_empty, sum_singleton] at hs ⊢
    rw [hs]; abel
  · subst hd; simp only [ite_true, show ¬ T.d = T.c from Ne.symm hcd, ite_false, empty_union,
      sum_singleton] at hs ⊢
    rw [hs]; abel
  · simp only [hc, hd, ite_false, union_empty, sum_empty, add_zero, sub_zero, Ne.symm hc, Ne.symm hd] at hs ⊢
    rw [hs]

end TwoExit
end WaveTurbulence.MoleProp4
