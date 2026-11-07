/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualSharedTripleEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.CutLabelUniqueness
import Mathlib.Tactic

/-! # A genuine old three-edge cut minus a four-valent star

This gives the virtual triple used in the hard two-bridge case. Its
window is the old cut cardinality plus one, with arbitrary old charges.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def actualThreeCutSigns (M : Molecule V D) (x y z r s : D) : Fin 6 → Bool :=
  ![M.out x,M.out y,M.out z,M.out (M.mate x),M.out (M.mate r),M.out (M.mate s)]

/-- The central old cut and old star imply the virtual momentum row. -/
theorem three_cut_virtual_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {b : V} (hb : b ∈ M.atoms) {e₁ e₂ x r s : D}
    (h12 : e₁ ≠ e₂) (h1r : e₁ ≠ r) (h2r : e₂ ≠ r)
    (hs : s ∉ ({e₁,e₂,r} : Finset D))
    (h1x : e₁ ≠ M.mate x) (h2x : e₂ ≠ M.mate x)
    (hB : M.dartsAt b = {e₁,e₂,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {e₁,e₂,M.mate x})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    -(M.dartSign x • latticePoint L (κ x))-(M.dartSign r • latticePoint L (κ r))-
      M.dartSign s • latticePoint L (κ s) = (∑ v ∈ U, c v)-c b := by
  have hc := Degen.cut_momentum M hd U hU
  have hbq := momentum_of_dartsAt_quadruple M L hb h12 h1r h2r hs hB hd
  simp [hcut,h12,h1x,h2x,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  rw [← hc,← hbq]
  abel

/-- Subtracting the actual star energy costs one further old window. -/
theorem three_cut_virtual_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {b : V} (hb : b ∈ M.atoms) {e₁ e₂ x r s : D}
    (h12 : e₁ ≠ e₂) (h1r : e₁ ≠ r) (h2r : e₂ ≠ r)
    (hs : s ∉ ({e₁,e₂,r} : Finset D))
    (h1x : e₁ ≠ M.mate x) (h2x : e₂ ≠ M.mate x)
    (hB : M.dartsAt b = {e₁,e₂,r,s}) (U : Finset V) (hU : U ⊆ M.atoms)
    (hcut : Degen.boundaryDarts M U = {e₁,e₂,M.mate x})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |-(M.dartSign x*‖latticePoint L (κ x)‖^2)-M.dartSign r*‖latticePoint L (κ r)‖^2-
      M.dartSign s*‖latticePoint L (κ s)‖^2-((∑ v ∈ U, β v)-β b)| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  have hc := Degen.cut_energy M hd hr U hU
  have hbq := energy_of_dartsAt_quadruple M L γ δ hb h12 h1r h2r hs hB hr
  simp [hcut,h12,h1x,h2x,Molecule.kvec,hd.1,Degen.dartSign_mate] at hc
  have hh := (abs_sub _ _).trans (add_le_add hc hbq)
  convert hh using 1 <;> congr 1 <;> ring

/-- A two-edge old leaf cut fixes the bridge label whenever its first-star
label is fixed. This is an actual old-charge argument. -/
theorem three_cut_leaf_label_unique (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (U : Finset V) (hU : U ⊆ M.atoms) (e y : D)
    (hcut : Degen.boundaryDarts M U = {M.mate e,M.mate y}) (hy : κ y=κ' y) : κ e=κ' e := by
  have hh : κ (M.mate e)=κ' (M.mate e) := by
    apply cut_label_unique_of_other_labels M hL hd hd' U hU (M.mate e)
    · rw [hcut]; exact mem_insert_self _ _
    · intro z hz hne
      rw [hcut] at hz
      rcases mem_insert.mp hz with he | hyz
      · exact (hne he).elim
      · rw [mem_singleton.mp hyz,hd.1,hd'.1,hy]
  simpa only [hd.1,hd'.1] using hh

/-- Both source rows, including the virtual row, are consequences of the
old graph's actual momentum equations. -/
theorem three_cut_shared_physical (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {e₁ e₂ x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : e₁ ≠ e₂) (h1r : e₁ ≠ r) (h2r : e₂ ≠ r)
    (hs : s ∉ ({e₁,e₂,r} : Finset D))
    (h1x : e₁ ≠ M.mate x) (h2x : e₂ ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {e₁,e₂,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {e₁,e₂,M.mate x})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i •
      latticePoint L (doubleFiveProfile x y z r s κ i)) =
      if second then (∑ v ∈ U, c v)-c b else c a := by
  cases second
  · have hh := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA hd
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,add_assoc] using hh
  · have hh := three_cut_virtual_momentum M L hb h12 h1r h2r hs h1x h2x hB U hU hcut hd
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,Degen.dartSign_mate,neg_smul,sub_eq_add_neg,add_assoc] using hh

theorem three_cut_shared_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    (hτ : 0 ≤ δ⁻¹*L^(-2*γ))
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {e₁ e₂ x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : e₁ ≠ e₂) (h1r : e₁ ≠ r) (h2r : e₂ ≠ r)
    (hs : s ∉ ({e₁,e₂,r} : Finset D))
    (h1x : e₁ ≠ M.mate x) (h2x : e₂ ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {e₁,e₂,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {e₁,e₂,M.mate x})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ)
    (second : Bool) :
    |(∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i •
      ‖latticePoint L (doubleFiveProfile x y z r s κ i)‖^2)-
      (if second then (∑ v ∈ U, β v)-β b else β a)| ≤
      ((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ)) := by
  cases second
  · have hh := energy_of_dartsAt_triple M L γ δ ha hxy hxz hyz hA hr
    have hN : (1 : ℝ) ≤ (U.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hle := mul_le_mul_of_nonneg_right hN hτ
    rw [one_mul] at hle
    have hh' := hh.trans hle
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,add_assoc] using hh'
  · have hh := three_cut_virtual_energy M L γ δ hb h12 h1r h2r hs h1x h2x hB U hU hcut hd hr
    simpa [sharedCoefficients,actualThreeCutSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,Degen.dartSign_mate,neg_mul,sub_eq_add_neg,add_assoc] using hh

theorem three_cut_shared_integer_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {e₁ e₂ x y z r s : D}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h12 : e₁ ≠ e₂) (h1r : e₁ ≠ r) (h2r : e₂ ≠ r)
    (hs : s ∉ ({e₁,e₂,r} : Finset D))
    (h1x : e₁ ≠ M.mate x) (h2x : e₂ ≠ M.mate x)
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {e₁,e₂,r,s})
    (U : Finset V) (hU : U ⊆ M.atoms) (hcut : Degen.boundaryDarts M U = {e₁,e₂,M.mate x})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i • doubleFiveProfile x y z r s κ i) =
      ∑ i : Fin 5, sharedCoefficients (actualThreeCutSigns M x y z r s) second i • doubleFiveProfile x y z r s κ0 i := by
  apply latticePointHom_injective hL
  simp only [map_sum,map_zsmul,latticePointHom_apply]
  exact (three_cut_shared_physical M L ha hb hxy hxz hyz h12 h1r h2r hs h1x h2x hA hB U hU hcut hd second).trans
    (three_cut_shared_physical M L ha hb hxy hxz hyz h12 h1r h2r hs h1x h2x hA hB U hU hcut hd0 second).symm

/-- The five-label profile determines all actual deleted labels: the two
remaining bridge labels are fixed by the old leaf cuts. -/
theorem three_cut_deletedLabels_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} {e₁ e₂ x y z r s : D}
    (hA : M.dartsAt a = {x,y,z}) (hB : M.dartsAt b = {e₁,e₂,r,s})
    (U₁ U₂ : Finset V) (hU₁ : U₁ ⊆ M.atoms) (hU₂ : U₂ ⊆ M.atoms)
    (hcut₁ : Degen.boundaryDarts M U₁ = {M.mate e₁,M.mate y})
    (hcut₂ : Degen.boundaryDarts M U₂ = {M.mate e₂,M.mate z})
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ')
    (hp : doubleFiveProfile x y z r s κ = doubleFiveProfile x y z r s κ') :
    deletedLabels M {a,b} κ = deletedLabels M {a,b} κ' := by
  have hx : κ x=κ' x := congrFun hp 0
  have hy : κ y=κ' y := congrFun hp 1
  have hz : κ z=κ' z := congrFun hp 2
  have hr : κ r=κ' r := congrFun hp 3
  have hs : κ s=κ' s := congrFun hp 4
  have he₁ := three_cut_leaf_label_unique M hL hd hd' U₁ hU₁ e₁ y hcut₁ hy
  have he₂ := three_cut_leaf_label_unique M hL hd hd' U₂ hU₂ e₂ z hcut₂ hz
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
      · exact he₁
      · exact he₂
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
