/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualThreeCutEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SevenLabelCount
import Mathlib.Tactic

/-! # Actual old three-edge cut equations in the post-removal beta case -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def actualSevenProfile {K : Type*} (x y z r s t u : D) (κ : D → K) : Fin 7 → K :=
  ![κ x,κ y,κ z,κ r,κ s,κ t,κ u]

theorem virtual_cut_shared_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a : V} (ha : a ∈ M.atoms) {x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hA : M.dartsAt a = {x,y,z}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate r,M.mate s})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i •
      latticePoint L (doubleFiveProfile x y z r s κ i)) =
      if second then ∑ v ∈ U, c v else c a := by
  cases second
  · have hh := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA hd
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,add_assoc] using hh
  · have hh := Degen.cut_momentum M hd U hU
    have hmr : M.mate x ≠ M.mate r := fun h => hxr (Mole.mate_injective M h)
    have hms : M.mate x ≠ M.mate s := fun h => hxs (Mole.mate_injective M h)
    have hmrs : M.mate r ≠ M.mate s := fun h => hrs (Mole.mate_injective M h)
    simp [hcut,hmr,hms,hmrs,Molecule.kvec,hd.1,Degen.dartSign_mate] at hh
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,Degen.dartSign_mate,neg_smul,sub_eq_add_neg,add_assoc] using hh

theorem virtual_cut_shared_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    (hτ : 0 ≤ δ⁻¹*L^(-2*γ)) {a : V} (ha : a ∈ M.atoms) {x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hA : M.dartsAt a = {x,y,z}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate r,M.mate s})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ)
    (second : Bool) :
    |(∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i •
      ‖latticePoint L (doubleFiveProfile x y z r s κ i)‖^2)-
      (if second then ∑ v ∈ U, β v else β a)| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  cases second
  · have hh := energy_of_dartsAt_triple M L γ δ ha hxy hxz hyz hA hr
    have hN : (1 : ℝ) ≤ (U.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hle := mul_le_mul_of_nonneg_right hN hτ
    rw [one_mul] at hle
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,add_assoc] using hh.trans hle
  · have hh := Degen.cut_energy M hd hr U hU
    have hmr : M.mate x ≠ M.mate r := fun h => hxr (Mole.mate_injective M h)
    have hms : M.mate x ≠ M.mate s := fun h => hxs (Mole.mate_injective M h)
    have hmrs : M.mate r ≠ M.mate s := fun h => hrs (Mole.mate_injective M h)
    simp [hcut,hmr,hms,hmrs,Molecule.kvec,hd.1,Degen.dartSign_mate] at hh
    have hle : (U.card : ℝ)*(δ⁻¹*L^(-2*γ)) ≤ ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hτ
    simp only [neg_mul] at hle
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,Degen.dartSign_mate,neg_mul,sub_eq_add_neg,add_assoc] using hh.trans hle

theorem virtual_cut_shared_integer_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a : V} (ha : a ∈ M.atoms) {x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hA : M.dartsAt a = {x,y,z}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate r,M.mate s})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i • doubleFiveProfile x y z r s κ i) =
      ∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i • doubleFiveProfile x y z r s κ0 i := by
  apply latticePointHom_injective hL
  simp only [map_sum,map_zsmul,latticePointHom_apply]
  exact (virtual_cut_shared_momentum M L ha hxy hxz hyz hxr hxs hrs hA U hU hcut hd second).trans
    (virtual_cut_shared_momentum M L ha hxy hxz hyz hxr hxs hrs hA U hU hcut hd0 second).symm

end WaveTurbulence.MoleProp
