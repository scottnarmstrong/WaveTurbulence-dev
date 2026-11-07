/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalConservation
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
public import WaveTurbulence.Foundations.FinalCount.AppBSignedPairNormalization
import Mathlib.Tactic

/-! # Two-bond local coordinates without orientation assumptions -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset

/-- The two actual outgoing labels, retaining the figure enumeration. -/
def appbTwoTuple {K : Type*} {n : ℕ} (h : n = 2) (q : Fin n → K) : K × K :=
  (q (Fin.cast h.symm 0),q (Fin.cast h.symm 1))

theorem appbTwoTuple_injective {K : Type*} {n : ℕ} (h : n = 2) :
    Function.Injective (appbTwoTuple (K := K) h) := by
  subst n
  intro q q' he
  funext i
  fin_cases i
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem appb_sum_fin_two {E : Type*} [AddCommMonoid E] {n : ℕ} (h : n = 2) (f : Fin n → E) :
    (∑ i,f i) = f (Fin.cast h.symm 0)+f (Fin.cast h.symm 1) := by
  subst n
  exact Fin.sum_univ_two f

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Exact signed momentum for a two-bond deletion, derived from the actual
incidence enumeration. The premises are finite graph typing data. -/
theorem two_bond_momentum (h : P.edges.length = 2) {v : V} (hv : v ∈ r.removedAtoms)
    (hinc : ∀ i, appbIncidence M v (r.edge i).val = 1)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) :
    let i := Fin.cast h.symm 0
    let j := Fin.cast h.symm 1
    (appbIncidenceSign M v (r.edge i).val : ℤ) • Molecule.kvec L w (r.localLabels κ) i +
      (appbIncidenceSign M v (r.edge j).val : ℤ) • Molecule.kvec L w (r.localLabels κ) j = c v := by
  have hm := r.local_momentum L w c κ hκ hv
  rw [appb_sum_fin_two h] at hm
  simpa only [appb_incidence_sign_eq M v _ (hinc _)] using hm

/-- Exact signed energy tolerance for the same actual two bonds. -/
theorem two_bond_energy (h : P.edges.length = 2) {v : V} (hv : v ∈ r.removedAtoms)
    (hinc : ∀ i, appbIncidence M v (r.edge i).val = 1)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    let i := Fin.cast h.symm 0
    let j := Fin.cast h.symm 1
    |(appbIncidenceSign M v (r.edge i).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) i‖^2 +
      (appbIncidenceSign M v (r.edge j).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) j‖^2-β v| ≤
      δ⁻¹*L^(-2*γ) := by
  have he := r.local_energy L γ δ w c β k0 κ hκ hres hv
  rw [appb_sum_fin_two h] at he
  simpa only [appb_incidence_sign_eq M v _ (hinc _),zsmul_eq_mul] using he

end AppbRealization
end WaveTurbulence.Mole
