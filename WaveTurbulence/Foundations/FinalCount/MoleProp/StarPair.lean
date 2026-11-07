/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SharpPositivePair
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # The actual two-incidence source equations, for both sign patterns -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def pairUnit (b b' : Bool) : ℤˣ := if b = b' then 1 else -1

theorem latticePoint_pairUnit_add {d : ℕ} (L : ℝ) (b b' : Bool) (x y : Fin d → ℤ) :
    latticePoint L (x + (pairUnit b b' : ℤ) • y) =
      latticePoint L x + (pairUnit b b' : ℤ) • latticePoint L y := by
  cases b <;> cases b' <;> ext j <;>
    simp [pairUnit,latticePoint,PiLp.add_apply,PiLp.smul_apply,PiLp.neg_apply,Pi.add_apply,Pi.neg_apply] <;> ring

theorem ordered_pair_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 2 ≃ IncidentDart M v)
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    latticePoint L (κ (e 0).val) +
      (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • latticePoint L (κ (e 1).val) =
        if M.out (e 0).val then c v else -c v := by
  have h := ordered_star_momentum M L (0 : Mom d) hv e hd
  simp only [Fin.sum_univ_two] at h
  cases h0 : M.out (e 0).val <;> cases h1 : M.out (e 1).val
  · simp [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] at h ⊢
    rw [← h]; abel
  · simp [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] at h ⊢
    rw [← h]; abel
  · simpa [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec,sub_eq_add_neg] using h
  · simpa [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] using h

theorem ordered_pair_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 2 ≃ IncidentDart M v)
    {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |‖latticePoint L (κ (e 0).val)‖ ^ 2 +
      (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) * ‖latticePoint L (κ (e 1).val)‖ ^ 2 -
      (if M.out (e 0).val then β v else -β v)| ≤ δ⁻¹ * L ^ (-2*γ) := by
  have h := ordered_star_energy M L γ δ (0 : Mom d) hv e hr
  simp only [Fin.sum_univ_two] at h
  cases h0 : M.out (e 0).val <;> cases h1 : M.out (e 1).val
  · simp [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] at h ⊢
    rw [← abs_neg] at h
    convert h using 1 <;> congr 1 <;> ring
  · simp [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] at h ⊢
    rw [← abs_neg] at h
    convert h using 1 <;> congr 1 <;> ring
  · simpa [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec,sub_eq_add_neg] using h
  · simpa [Molecule.dartSign,pairUnit,h0,h1,Molecule.kvec] using h

theorem ordered_pair_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) {v : V} (hv : v ∈ M.atoms) (e : Fin 2 ≃ IncidentDart M v)
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ') :
    κ (e 0).val + (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • κ (e 1).val =
      κ' (e 0).val + (pairUnit (M.out (e 0).val) (M.out (e 1).val) : ℤ) • κ' (e 1).val := by
  have h := (ordered_pair_momentum M L hv e hd).trans (ordered_pair_momentum M L hv e hd').symm
  apply Degen.coset_label_injective hL (0 : Mom d)
  simpa only [zero_add,latticePoint_pairUnit_add] using h

theorem starPair_injective (M : Molecule V D) (v : V) (e : Fin 2 ≃ IncidentDart M v)
    {K : Type*} : Function.Injective (fun q : IncidentDart M v → K => (q (e 0),q (e 1))) := by
  intro q q' h
  funext x
  obtain ⟨i,rfl⟩ := e.surjective x
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

end WaveTurbulence.MoleProp
