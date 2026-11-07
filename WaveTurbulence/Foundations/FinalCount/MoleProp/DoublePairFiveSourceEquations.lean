/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSourceEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveSignedCount
import Mathlib.Tactic

/-! # Actual three/four-valent stars give the five-label source equations

All equations come from the original graph decoration and its genuine
energy restrictions. Nonzero charges at four-valent atoms are retained.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def doubleFiveProfile {K : Type*} (x y r s t : D) (κ : D → K) : Fin 5 → K :=
  ![κ x,κ y,κ r,κ s,κ t]

@[simp] theorem doubleFiveProfile_zero {K : Type*} (x y r s t : D) (κ : D → K) :
    doubleFiveProfile x y r s t κ 0 = κ x := rfl
@[simp] theorem doubleFiveProfile_one {K : Type*} (x y r s t : D) (κ : D → K) :
    doubleFiveProfile x y r s t κ 1 = κ y := rfl
@[simp] theorem doubleFiveProfile_two {K : Type*} (x y r s t : D) (κ : D → K) :
    doubleFiveProfile x y r s t κ 2 = κ r := rfl
@[simp] theorem doubleFiveProfile_three {K : Type*} (x y r s t : D) (κ : D → K) :
    doubleFiveProfile x y r s t κ 3 = κ s := rfl
@[simp] theorem doubleFiveProfile_four {K : Type*} (x y r s t : D) (κ : D → K) :
    doubleFiveProfile x y r s t κ 4 = κ t := rfl

theorem source_double_five_physical_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (ht : t ∉ ({M.mate x,M.mate y,s} : Finset D))
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s,t})
    (ho : M.out s = !M.out r) (hto : M.out t = doubleExtraSign (M.out x) (M.out y) (M.out r))
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    SignedDoubleFiveMomentum (M.out x) (M.out y) (M.out r) (c a) (c b)
      (fun i => latticePoint L (doubleFiveProfile x y r s t κ i)) := by
  have hpa := momentum_of_dartsAt_triple M L ha hxy hxr hyr hA hd
  have hpb := momentum_of_dartsAt_quadruple M L hb hmxy hmxs hmys ht hB hd
  have hext : doubleSign (doubleExtraSign (M.out x) (M.out y) (M.out r)) • latticePoint L (κ t) =
      M.dartSign t • latticePoint L (κ t) := by
    rw [← hto]
    exact doubleSign_out_smul M t _
  constructor
  · simpa only [doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_two,doubleSign_out_smul] using hpa
  · simpa only [doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_three,doubleFiveProfile_four,
      doubleSign_out_smul,hext,hd.1,Degen.dartSign_mate,dartSign_of_opposite_out M ho,neg_smul,sub_eq_add_neg] using hpb

theorem source_double_five_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (ht : t ∉ ({M.mate x,M.mate y,s} : Finset D))
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s,t})
    (ho : M.out s = !M.out r) (hto : M.out t = doubleExtraSign (M.out x) (M.out y) (M.out r))
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |signedDoubleFiveEnergyOne (M.out x) (M.out y) (M.out r)
      (fun i => latticePoint L (doubleFiveProfile x y r s t κ i))-β a| ≤ δ⁻¹*L^(-2*γ) ∧
    |signedDoubleFiveEnergyTwo (M.out x) (M.out y) (M.out r)
      (fun i => latticePoint L (doubleFiveProfile x y r s t κ i))-β b| ≤ δ⁻¹*L^(-2*γ) := by
  have hpa := energy_of_dartsAt_triple M L γ δ ha hxy hxr hyr hA hr
  have hpb := energy_of_dartsAt_quadruple M L γ δ hb hmxy hmxs hmys ht hB hr
  have hext : ((doubleSign (doubleExtraSign (M.out x) (M.out y) (M.out r)) : ℤ) : ℝ) = M.dartSign t := by
    rw [← hto]
    exact doubleSign_out_cast M t
  constructor
  · simpa only [signedDoubleFiveEnergyOne,doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_two,doubleSign_out_cast] using hpa
  · simpa only [signedDoubleFiveEnergyTwo,doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_three,doubleFiveProfile_four,
      doubleSign_out_cast,hext,hd.1,Degen.dartSign_mate,dartSign_of_opposite_out M ho,neg_mul,sub_eq_add_neg] using hpb

/-- Arbitrary fixed physical charges fix the two literal integer momentum
parameters on the actual old counting fiber. -/
theorem source_double_five_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hmxy : M.mate x ≠ M.mate y) (hmxs : M.mate x ≠ s) (hmys : M.mate y ≠ s)
    (ht : t ∉ ({M.mate x,M.mate y,s} : Finset D))
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,M.mate y,s,t})
    (ho : M.out s = !M.out r) (hto : M.out t = doubleExtraSign (M.out x) (M.out y) (M.out r))
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    SignedDoubleFiveMomentum (M.out x) (M.out y) (M.out r)
      (doubleSign (M.out x) • κ0 x+doubleSign (M.out y) • κ0 y+doubleSign (M.out r) • κ0 r)
      (-(doubleSign (M.out x) • κ0 x)-doubleSign (M.out y) • κ0 y-doubleSign (M.out r) • κ0 s+
        doubleSign (doubleExtraSign (M.out x) (M.out y) (M.out r)) • κ0 t)
      (doubleFiveProfile x y r s t κ) := by
  have h := source_double_five_physical_momentum M L ha hb hxy hxr hyr hmxy hmxs hmys ht hA hB ho hto hd
  have h0 := source_double_five_physical_momentum M L ha hb hxy hxr hyr hmxy hmxs hmys ht hA hB ho hto hd0
  constructor
  · apply latticePointHom_injective hL
    simp only [map_add,map_zsmul,latticePointHom_apply]
    simpa only [doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_two] using h.1.trans h0.1.symm
  · apply latticePointHom_injective hL
    simp only [map_add,map_sub,map_neg,map_zsmul,latticePointHom_apply]
    simpa only [doubleFiveProfile_zero,doubleFiveProfile_one,doubleFiveProfile_three,doubleFiveProfile_four] using h.2.trans h0.2.symm

end WaveTurbulence.MoleProp
