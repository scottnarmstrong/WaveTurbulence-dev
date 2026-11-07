/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSourceEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadCount
import Mathlib.Tactic

/-! # A genuine old mixed cut gives the split-quad source constraints -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem mixed_cut_pair_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {x y : D} (hxy : x ≠ y) (hxo : M.out x = false) (hyo : M.out y = true)
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate y})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    latticePoint L (κ x)-latticePoint L (κ y) = ∑ a ∈ U, c a := by
  have hm := Degen.cut_momentum M hd U hU
  have hmate : M.mate x ≠ M.mate y := fun h => hxy (Mole.mate_injective M h)
  rw [hcut,sum_pair hmate] at hm
  simpa [Degen.dartSign_mate,Molecule.dartSign,M.out_mate,hxo,hyo,hd.1,Molecule.kvec,sub_eq_add_neg] using hm

theorem mixed_cut_pair_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {x y : D} (hxy : x ≠ y) (hxo : M.out x = false) (hyo : M.out y = true)
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate y})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} {β : V → ℝ} {k0 : D → Mom d}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |‖latticePoint L (κ x)‖^2-‖latticePoint L (κ y)‖^2-∑ a ∈ U, β a| ≤
      (U.card : ℝ)*(δ⁻¹*L^(-2*γ)) := by
  have hm := Degen.cut_energy M hd hr U hU
  have hmate : M.mate x ≠ M.mate y := fun h => hxy (Mole.mate_injective M h)
  rw [hcut,sum_pair hmate] at hm
  simpa [Degen.dartSign_mate,Molecule.dartSign,M.out_mate,hxo,hyo,hd.1,Molecule.kvec,sub_eq_add_neg] using hm

theorem split_quad_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {v : V} (hv : v ∈ M.atoms) {x y r s : D} (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hs : s ∉ ({x,y,r} : Finset D)) (hstar : M.dartsAt v = {x,y,r,s})
    (hxo : M.out x = false) (hyo : M.out y = true) (hro : M.out r = false) (hso : M.out s = true)
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate y})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    κ x-κ y=κ0 x-κ0 y ∧ κ r-κ s=κ0 r-κ0 s := by
  have h1 : κ x-κ y=κ0 x-κ0 y := by
    apply latticePointHom_injective hL
    simp only [map_sub,latticePointHom_apply]
    exact (mixed_cut_pair_momentum M L hxy hxo hyo U hU hcut hd).trans
      (mixed_cut_pair_momentum M L hxy hxo hyo U hU hcut hd0).symm
  have hfull {κ} (hD : M.IsDecoration L (0 : Mom d) c κ) :
      latticePoint L ((κ x-κ y)+(κ r-κ s)) = -c v := by
    have hm := momentum_of_dartsAt_quadruple M L hv hxy hxr hyr hs hstar hD
    simp only [Molecule.dartSign,hxo,hyo,hro,hso,Bool.false_eq_true,ite_false,ite_true,neg_one_smul,one_smul] at hm
    rw [WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq,← hm]
    abel
  have ht : (κ x-κ y)+(κ r-κ s) = (κ0 x-κ0 y)+(κ0 r-κ0 s) :=
    latticePointHom_injective hL ((hfull hd).trans (hfull hd0).symm)
  exact ⟨h1,by rw [h1] at ht; exact add_left_cancel ht⟩

theorem split_quad_energy (M : Molecule V D) {d : ℕ} {L γ δ : ℝ}
    (hτ : 0 ≤ δ⁻¹*L^(-2*γ)) {v : V} (hv : v ∈ M.atoms)
    {x y r s : D} (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hs : s ∉ ({x,y,r} : Finset D)) (hstar : M.dartsAt v = {x,y,r,s})
    (hxo : M.out x = false) (hyo : M.out y = true) (hro : M.out r = false) (hso : M.out s = true)
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {M.mate x,M.mate y})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} {β : V → ℝ} {k0 : D → Mom d}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |‖latticePoint L (κ x)‖^2-‖latticePoint L (κ y)‖^2-∑ a ∈ U, β a| ≤
        ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) ∧
      |‖latticePoint L (κ r)‖^2-‖latticePoint L (κ s)‖^2-(-β v-∑ a ∈ U, β a)| ≤
        ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  have hc := mixed_cut_pair_energy M L γ δ hxy hxo hyo U hU hcut hd hr
  have hvE := energy_of_dartsAt_quadruple M L γ δ hv hxy hxr hyr hs hstar hr
  simp only [Molecule.dartSign,hxo,hyo,hro,hso,Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul] at hvE
  constructor
  · exact hc.trans (by nlinarith only [hτ])
  · obtain ⟨hcL,hcR⟩ := abs_le.mp hc
    obtain ⟨hvL,hvR⟩ := abs_le.mp hvE
    apply abs_le.mpr
    constructor <;> linarith only [hcL,hcR,hvL,hvR]

end WaveTurbulence.MoleProp
