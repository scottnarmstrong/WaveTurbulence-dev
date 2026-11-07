/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualThreeCutEquations
import Mathlib.Tactic

/-! # An old pair cut and a cubic star produce a virtual cubic star

The cut side contains the second star, so subtracting its conservation
row cancels the bridge label. All charges are the original old charges.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def actualAffineInsideSigns (M : Molecule V D) (x y z r s : D) : Fin 6 → Bool :=
  ![M.out x,M.out y,M.out z,M.out x,M.out r,M.out s]

theorem affine_inside_virtual_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {b : V} (hb : b ∈ M.atoms) {p x r s : D}
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s) (hpx : p ≠ M.mate x)
    (hB : M.dartsAt b = {p,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    M.dartSign x • latticePoint L (κ x)+M.dartSign r • latticePoint L (κ r)+
      M.dartSign s • latticePoint L (κ s) = c b-(∑ v ∈ U, c v) := by
  have hc := Degen.cut_momentum M hd U hU
  have hbq := momentum_of_dartsAt_triple M L hb hpr hps hrs hB hd
  simp [hcut,hpx,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  rw [← hc,← hbq]
  abel

theorem affine_inside_virtual_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {b : V} (hb : b ∈ M.atoms) {p x r s : D}
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s) (hpx : p ≠ M.mate x)
    (hB : M.dartsAt b = {p,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |M.dartSign x*‖latticePoint L (κ x)‖^2+M.dartSign r*‖latticePoint L (κ r)‖^2+
      M.dartSign s*‖latticePoint L (κ s)‖^2-(β b-(∑ v ∈ U, β v))| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  have hc := Degen.cut_energy M hd hr U hU
  have hbq := energy_of_dartsAt_triple M L γ δ hb hpr hps hrs hB hr
  simp [hcut,hpx,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  have hh := (abs_sub _ _).trans (add_le_add hbq hc)
  convert hh using 1 <;> congr 1 <;> ring

theorem affine_inside_physical (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s) (hpx : p ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualAffineInsideSigns M x y z r s) second i •
      latticePoint L (doubleFiveProfile x y z r s κ i)) =
      if second then c b-(∑ v ∈ U, c v) else c a := by
  cases second
  · have hh := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA hd
    simpa [sharedCoefficients,actualAffineInsideSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,add_assoc] using hh
  · have hh := affine_inside_virtual_momentum M L hb hpr hps hrs hpx hB U hU hcut hd
    simpa [sharedCoefficients,actualAffineInsideSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,Degen.dartSign_mate,neg_smul,add_assoc] using hh

theorem affine_inside_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    (hτ : 0 ≤ δ⁻¹*L^(-2*γ))
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s) (hpx : p ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ)
    (second : Bool) :
    |(∑ i : Fin 5, sharedCoefficients (actualAffineInsideSigns M x y z r s) second i •
      ‖latticePoint L (doubleFiveProfile x y z r s κ i)‖^2)-
      (if second then β b-(∑ v ∈ U, β v) else β a)| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  cases second
  · have hh := energy_of_dartsAt_triple M L γ δ ha hxy hxz hyz hA hr
    have hN : (1 : ℝ) ≤ (U.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hle := mul_le_mul_of_nonneg_right hN hτ
    rw [one_mul] at hle
    have hh' := hh.trans hle
    simpa [sharedCoefficients,actualAffineInsideSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,add_assoc] using hh'
  · have hh := affine_inside_virtual_energy M L γ δ hb hpr hps hrs hpx hB U hU hcut hd hr
    simpa [sharedCoefficients,actualAffineInsideSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,Degen.dartSign_mate,neg_mul,add_assoc] using hh

theorem affine_inside_integer_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {p x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s) (hpx : p ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualAffineInsideSigns M x y z r s) second i • doubleFiveProfile x y z r s κ i) =
      ∑ i : Fin 5, sharedCoefficients (actualAffineInsideSigns M x y z r s) second i • doubleFiveProfile x y z r s κ0 i := by
  apply latticePointHom_injective hL
  simp only [map_sum,map_zsmul,latticePointHom_apply]
  exact (affine_inside_physical M L ha hb hxy hxz hyz hpr hps hrs hpx hA hB U hU hcut hd second).trans
    (affine_inside_physical M L ha hb hxy hxz hyz hpr hps hrs hpx hA hB U hU hcut hd0 second).symm

theorem affine_inside_deletedLabels_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} {p x y z r s : D}
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {p,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {p,M.mate x})
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (hp : doubleFiveProfile x y z r s κ = doubleFiveProfile x y z r s κ') :
    deletedLabels M {a,b} κ = deletedLabels M {a,b} κ' := by
  have hx : κ x=κ' x := congrFun hp 0
  have hy : κ y=κ' y := congrFun hp 1
  have hz : κ z=κ' z := congrFun hp 2
  have hr : κ r=κ' r := congrFun hp 3
  have hs : κ s=κ' s := congrFun hp 4
  have hep : κ p=κ' p := by
    apply cut_label_unique_of_other_labels M hL hd hd' U hU p
    · rw [hcut]; exact mem_insert_self _ _
    · intro w hw hne
      rw [hcut] at hw
      rcases mem_insert.mp hw with hw | hw
      · exact (hne hw).elim
      · rw [mem_singleton.mp hw,hd.1,hd'.1,hx]
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
      rcases hw' with rfl | rfl | rfl
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
