/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingCutEnergy
import Mathlib.Tactic

/-! # Actual three-bond cuts and their signed conservation equations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure AppbCutTriple {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (S : Finset V) where
  subset_atoms : S ⊆ M.atoms
  crossing : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms
  index : Fin 3 ↪ Fin P.edges.length
  cross : ∀ j,(M.atom (r.edge (index j)).val ∈ S ∧ M.atom (M.mate (r.edge (index j)).val) ∉ S) ∨
    (M.atom (r.edge (index j)).val ∉ S ∧ M.atom (M.mate (r.edge (index j)).val) ∈ S)
  other : ∀ i,(∀ j,index j ≠ i) → (M.atom (r.edge i).val ∈ S ↔ M.atom (M.mate (r.edge i).val) ∈ S)

namespace AppbCutTriple
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (t : AppbCutTriple r S)

theorem sum_index {E : Type*} [AddCommMonoid E] (f : Fin P.edges.length → E)
    (hz : ∀ i,(∀ j,t.index j ≠ i) → f i = 0) :
    (∑ i,f i) = ∑ j : Fin 3,f (t.index j) := by
  classical
  have hh : (∑ i ∈ (univ : Finset (Fin 3)).image t.index,f i) = ∑ j : Fin 3,f (t.index j) :=
    sum_image (fun a _ b _ h => t.index.injective h)
  rw [← hh]
  symm
  apply sum_subset (subset_univ _)
  intro i hi hn
  apply hz i
  intro j hj
  exact hn (mem_image.mpr ⟨j,mem_univ _,hj⟩)

theorem sum_contribution {E : Type*} [AddCommGroup E] (f : Fin P.edges.length → E) :
    (∑ i,((if M.atom (r.edge i).val ∈ S then f i else 0)-
      (if M.atom (M.mate (r.edge i).val) ∈ S then f i else 0))) =
      ∑ j : Fin 3,(appbCutSign M S (r.edge (t.index j)).val : ℤ) • f (t.index j) := by
  rw [t.sum_index]
  · apply sum_congr rfl
    intro j hj
    exact appb_cut_sign_eq M S _ (t.cross j) _
  · intro i hi
    have hh := t.other i hi
    by_cases ha : M.atom (r.edge i).val ∈ S
    · simp only [ha,hh.mp ha,ite_true,sub_self]
    · have hb : M.atom (M.mate (r.edge i).val) ∉ S := fun hb => ha (hh.mpr hb)
      simp only [ha,hb,ite_false,sub_zero]

theorem momentum {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) :
    (∑ j : Fin 3,(appbCutSign M S (r.edge (t.index j)).val : ℤ) • Molecule.kvec L w (r.localLabels κ) (t.index j)) =
      ∑ v ∈ S,c v := by
  have hh := r.cut_momentum S t.subset_atoms t.crossing L w c κ hκ
  rw [t.sum_contribution] at hh
  exact hh

theorem energy {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ)
    (hres : M.IsRestricted L γ δ w β k0 κ) :
    |(∑ j : Fin 3,(appbCutSign M S (r.edge (t.index j)).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) (t.index j)‖^2)-
      ∑ v ∈ S,β v| ≤ S.card*(δ⁻¹*L^(-2*γ)) := by
  have hh := r.cut_energy S t.subset_atoms t.crossing L γ δ w c β k0 κ hκ hres
  rw [t.sum_contribution] at hh
  simpa only [zsmul_eq_mul] using hh

end AppbCutTriple
end WaveTurbulence.Mole
