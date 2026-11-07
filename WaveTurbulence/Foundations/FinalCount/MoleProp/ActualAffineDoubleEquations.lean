/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualAffineSharedEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoubleSharedCount
import Mathlib.Tactic

/-! # A pair cut and a neighboring quartic star give a virtual quad

The two shared labels are distinct first-star positions. No balance
assumption is imposed on the resulting virtual quad.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem affine_double_virtual_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {b : V} (hb : b ∈ M.atoms) {p x y r s : D}
    (hxp : M.mate x ≠ p) (hxr : M.mate x ≠ r) (hpr : p ≠ r)
    (hs : s ∉ ({M.mate x,p,r} : Finset D)) (hpy : p ≠ y)
    (hB : M.dartsAt b = {M.mate x,p,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    -(M.dartSign x • latticePoint L (κ x))-(M.dartSign y • latticePoint L (κ y))+
      M.dartSign r • latticePoint L (κ r)+M.dartSign s • latticePoint L (κ s) =
      (∑ v ∈ U, c v)+c b := by
  have hc := Degen.cut_momentum M hd U hU
  have hbq := momentum_of_dartsAt_quadruple M L hb hxp hxr hpr hs hB hd
  have hmpy : M.mate p ≠ M.mate y := fun h => hpy (Mole.mate_injective M h)
  simp [hcut,hmpy,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  simp only [hd.1,Degen.dartSign_mate,neg_smul] at hbq
  rw [← hc,← hbq]
  abel

theorem affine_double_virtual_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {b : V} (hb : b ∈ M.atoms) {p x y r s : D}
    (hxp : M.mate x ≠ p) (hxr : M.mate x ≠ r) (hpr : p ≠ r)
    (hs : s ∉ ({M.mate x,p,r} : Finset D)) (hpy : p ≠ y)
    (hB : M.dartsAt b = {M.mate x,p,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |-(M.dartSign x*‖latticePoint L (κ x)‖^2)-M.dartSign y*‖latticePoint L (κ y)‖^2+
      M.dartSign r*‖latticePoint L (κ r)‖^2+M.dartSign s*‖latticePoint L (κ s)‖^2-
      ((∑ v ∈ U, β v)+β b)| ≤ ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  have hc := Degen.cut_energy M hd hr U hU
  have hbq := energy_of_dartsAt_quadruple M L γ δ hb hxp hxr hpr hs hB hr
  have hmpy : M.mate p ≠ M.mate y := fun h => hpy (Mole.mate_injective M h)
  simp [hcut,hmpy,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  simp only [hd.1,Degen.dartSign_mate,neg_mul] at hbq
  have hh := (abs_add_le _ _).trans (add_le_add hc hbq)
  convert hh using 1 <;> congr 1 <;> ring

theorem affine_double_physical (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : M.mate x ≠ p) (hxr : M.mate x ≠ r) (hpr : p ≠ r)
    (hs : s ∉ ({M.mate x,p,r} : Finset D)) (hpy : p ≠ y)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {M.mate x,p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (second : Bool) :
    (∑ i : Fin 5, doubleSharedCoefficients (![M.out x,M.out y,M.out z,M.out r,M.out s]) second i •
      latticePoint L (doubleFiveProfile x y z r s κ i)) =
      if second then (∑ v ∈ U, c v)+c b else c a := by
  cases second
  · have hh := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA hd
    simpa [doubleSharedCoefficients,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,add_assoc] using hh
  · have hh := affine_double_virtual_momentum M L hb hxp hxr hpr hs hpy hB U hU hcut hd
    simpa [doubleSharedCoefficients,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,neg_smul,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

theorem affine_double_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    (hτ : 0 ≤ δ⁻¹*L^(-2*γ))
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : M.mate x ≠ p) (hxr : M.mate x ≠ r) (hpr : p ≠ r)
    (hs : s ∉ ({M.mate x,p,r} : Finset D)) (hpy : p ≠ y)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {M.mate x,p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ)
    (second : Bool) :
    |(∑ i : Fin 5, doubleSharedCoefficients (![M.out x,M.out y,M.out z,M.out r,M.out s]) second i •
      ‖latticePoint L (doubleFiveProfile x y z r s κ i)‖^2)-
      (if second then (∑ v ∈ U, β v)+β b else β a)| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  cases second
  · have hh := energy_of_dartsAt_triple M L γ δ ha hxy hxz hyz hA hr
    have hN : (1 : ℝ) ≤ (U.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hle := mul_le_mul_of_nonneg_right hN hτ
    rw [one_mul] at hle
    have hh' := hh.trans hle
    simpa [doubleSharedCoefficients,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,add_assoc] using hh'
  · have hh := affine_double_virtual_energy M L γ δ hb hxp hxr hpr hs hpy hB U hU hcut hd hr
    simpa [doubleSharedCoefficients,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

theorem affine_double_integer_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxp : M.mate x ≠ p) (hxr : M.mate x ≠ r) (hpr : p ≠ r)
    (hs : s ∉ ({M.mate x,p,r} : Finset D)) (hpy : p ≠ y)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {M.mate x,p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0)
    (second : Bool) :
    (∑ i : Fin 5, doubleSharedCoefficients (![M.out x,M.out y,M.out z,M.out r,M.out s]) second i • doubleFiveProfile x y z r s κ i) =
      ∑ i : Fin 5, doubleSharedCoefficients (![M.out x,M.out y,M.out z,M.out r,M.out s]) second i • doubleFiveProfile x y z r s κ0 i := by
  apply latticePointHom_injective hL
  simp only [map_sum,map_zsmul,latticePointHom_apply]
  exact (affine_double_physical M L ha hb hxy hxz hyz hxp hxr hpr hs hpy hA hB U hU hcut hd second).trans
    (affine_double_physical M L ha hb hxy hxz hyz hxp hxr hpr hs hpy hA hB U hU hcut hd0 second).symm

theorem affine_double_deletedLabels_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} {p x y z r s : D}
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {M.mate x,p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {M.mate p,M.mate y})
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (hp : doubleFiveProfile x y z r s κ = doubleFiveProfile x y z r s κ') :
    deletedLabels M {a,b} κ = deletedLabels M {a,b} κ' := by
  have hx : κ x=κ' x := congrFun hp 0
  have hy : κ y=κ' y := congrFun hp 1
  have hz : κ z=κ' z := congrFun hp 2
  have hr : κ r=κ' r := congrFun hp 3
  have hs : κ s=κ' s := congrFun hp 4
  have hep := three_cut_leaf_label_unique M hL hd hd' U hU p y hcut hy
  have hAt : ∀ w : D, M.atom w ∈ ({a,b} : Finset V) → κ w=κ' w := by
    intro w hw
    rcases mem_insert.mp hw with hwa | hwb
    · have hw' := (Mole.mem_dartsAt M a w).mpr hwa
      rw [hA] at hw'
      simp only [mem_insert,mem_singleton] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    · have hw' := (Mole.mem_dartsAt M b w).mpr (mem_singleton.mp hwb)
      rw [hB] at hw'
      simp only [mem_insert,mem_singleton] at hw'
      rcases hw' with rfl | rfl | rfl | rfl
      · simpa only [hd.1,hd'.1] using hx
      · exact hep
      · exact hr
      · exact hs
  funext w
  change κ w.val=κ' w.val
  by_cases hw : M.atom w.val ∈ ({a,b} : Finset V)
  · exact hAt w.val hw
  · have hmate : M.atom (M.mate w.val) ∈ ({a,b} : Finset V) := by
      by_contra hh
      exact w.property ⟨hw,hh⟩
    simpa only [hd.1,hd'.1] using hAt (M.mate w.val) hmate


end WaveTurbulence.MoleProp
