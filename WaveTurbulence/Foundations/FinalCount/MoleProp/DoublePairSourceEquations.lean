/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairStars
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSignedCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LatticeHom
import Mathlib.Tactic

/-! # Actual paired degree-three stars give the literal signed source problem -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def doublePairProfile {K : Type*} (x y r s : D) (κ : D → K) : Fin 4 → K :=
  ![κ x,κ y,κ r,κ s]

@[simp] theorem doublePairProfile_zero {K : Type*} (x y r s : D) (κ : D → K) :
    doublePairProfile x y r s κ 0 = κ x := rfl
@[simp] theorem doublePairProfile_one {K : Type*} (x y r s : D) (κ : D → K) :
    doublePairProfile x y r s κ 1 = κ y := rfl
@[simp] theorem doublePairProfile_two {K : Type*} (x y r s : D) (κ : D → K) :
    doublePairProfile x y r s κ 2 = κ r := rfl
@[simp] theorem doublePairProfile_three {K : Type*} (x y r s : D) (κ : D → K) :
    doublePairProfile x y r s κ 3 = κ s := rfl

theorem doubleSign_out_cast (M : Molecule V D) (x : D) :
    ((doubleSign (M.out x) : ℤ) : ℝ) = M.dartSign x := by
  cases hx : M.out x <;> simp [doubleSign,Molecule.dartSign,hx]

theorem doubleSign_out_smul (M : Molecule V D) {d : ℕ} (x : D) (q : Mom d) :
    doubleSign (M.out x) • q = M.dartSign x • q := by
  cases hx : M.out x <;> simp [doubleSign,Molecule.dartSign,hx]

theorem dartSign_of_opposite_out (M : Molecule V D) {r s : D} (ho : M.out s = !M.out r) :
    M.dartSign s = -M.dartSign r := by
  unfold Molecule.dartSign
  rw [ho]
  cases M.out r <;> norm_num

theorem source_double_pair_physical_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s})
    (ho : M.out s = !M.out r) {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) :
    SignedDoublePairMomentum (M.out x) (M.out y) (M.out r) (c a) (c b)
      (fun i => latticePoint L (doublePairProfile x y r s κ i)) := by
  have hpa := momentum_of_dartsAt_triple M L ha hxy hxr hyr hA hd
  have hpb := momentum_of_dartsAt_triple M L hb hmxy hmxs hmys hB hd
  constructor
  · simpa only [doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three,doubleSign_out_smul] using hpa
  · simpa only [doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three,doubleSign_out_smul,
      hd.1,Degen.dartSign_mate,dartSign_of_opposite_out M ho,neg_smul,sub_eq_add_neg] using hpb

theorem source_double_pair_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s})
    (ho : M.out s = !M.out r) {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
    {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |signedDoubleEnergyOne (M.out x) (M.out y) (M.out r)
      (fun i => latticePoint L (doublePairProfile x y r s κ i))-β a| ≤ δ⁻¹*L^(-2*γ) ∧
    |signedDoubleEnergyTwo (M.out x) (M.out y) (M.out r)
      (fun i => latticePoint L (doublePairProfile x y r s κ i))-β b| ≤ δ⁻¹*L^(-2*γ) := by
  have hpa := energy_of_dartsAt_triple M L γ δ ha hxy hxr hyr hA hr
  have hpb := energy_of_dartsAt_triple M L γ δ hb hmxy hmxs hmys hB hr
  constructor
  · simpa only [signedDoubleEnergyOne,doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three,doubleSign_out_cast] using hpa
  · simpa only [signedDoubleEnergyTwo,doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three,doubleSign_out_cast,
      hd.1,Degen.dartSign_mate,dartSign_of_opposite_out M ho,neg_mul,sub_eq_add_neg] using hpb

/-- The frozen lattice embedding preserves every signed source sum. -/
theorem latticePoint_signed_double_sum {d : ℕ} (L : ℝ) (sx sy sr : Bool) (k : Fin 4 → (Fin d → ℤ)) :
    latticePoint L (doubleSign sx • k 0 + doubleSign sy • k 1 + doubleSign sr • k 2) =
      doubleSign sx • latticePoint L (k 0) + doubleSign sy • latticePoint L (k 1) + doubleSign sr • latticePoint L (k 2) := by
  simp only [WeylSums.latticePoint_add_eq,latticePoint_zsmul]

theorem latticePoint_signed_double_sum_two {d : ℕ} (L : ℝ) (sx sy sr : Bool) (k : Fin 4 → (Fin d → ℤ)) :
    latticePoint L (-(doubleSign sx • k 0) - doubleSign sy • k 1 - doubleSign sr • k 3) =
      -(doubleSign sx • latticePoint L (k 0)) - doubleSign sy • latticePoint L (k 1) - doubleSign sr • latticePoint L (k 3) := by
  change latticePointHom L (-(doubleSign sx • k 0)-doubleSign sy • k 1-doubleSign sr • k 3) = _
  simp only [map_sub,map_neg,map_zsmul,latticePointHom_apply]

/-- Fixed actual source charges give fixed integer momentum parameters
on the whole old counting fiber, without requiring a source charge to vanish. -/
theorem source_double_pair_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s})
    (ho : M.out s = !M.out r) {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    SignedDoublePairMomentum (M.out x) (M.out y) (M.out r)
      (doubleSign (M.out x) • κ0 x + doubleSign (M.out y) • κ0 y + doubleSign (M.out r) • κ0 r)
      (-(doubleSign (M.out x) • κ0 x)-doubleSign (M.out y) • κ0 y-doubleSign (M.out r) • κ0 s)
      (doublePairProfile x y r s κ) := by
  have h := source_double_pair_physical_momentum M L ha hb hxy hxr hyr hmxy hmxs hmys hA hB ho hd
  have h0 := source_double_pair_physical_momentum M L ha hb hxy hxr hyr hmxy hmxs hmys hA hB ho hd0
  constructor
  · apply latticePointHom_injective hL
    simp only [map_add,map_zsmul,latticePointHom_apply]
    simpa only [doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three] using h.1.trans h0.1.symm
  · apply latticePointHom_injective hL
    simp only [map_sub,map_neg,map_zsmul,latticePointHom_apply]
    simpa only [doublePairProfile_zero,doublePairProfile_one,doublePairProfile_two,doublePairProfile_three] using h.2.trans h0.2.symm

/-- The norm of the actual rail difference is the norm of the conserved
signed sum; the orientation contributes only an overall sign. -/
theorem signed_double_pair_charge_norm {d : ℕ} (L : ℝ) (sx sy sr : Bool)
    (a b : Fin d → ℤ) (k : Fin 4 → (Fin d → ℤ)) (h : SignedDoublePairMomentum sx sy sr a b k) :
    ‖latticePoint L (a+b)‖ = ‖latticePoint L (k 2)-latticePoint L (k 3)‖ := by
  have he : a+b = doubleSign sr • (k 2-k 3) := by
    rw [← h.1,← h.2,smul_sub]
    abel
  rw [he,latticePoint_zsmul,WeylSums.latticePoint_sub_eq]
  cases sr <;> simp [doubleSign,norm_sub_rev]

end WaveTurbulence.MoleProp
