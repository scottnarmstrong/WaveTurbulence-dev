/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineD
public import WaveTurbulence.Foundations.FinalCount.Case5Fin
import Mathlib.Tactic

/-! # Prop 9.6, case (5): a vine component has no `α`-atom (vineLG against alphaSG) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem vine_contra {d : ℕ} {M : Molecule V D} {cls : V → Cls} {odd : Prop} {L γ η : ℝ}
    {Adm : (D → (Fin d → ℤ)) → Prop} (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm)
    {κ : D → (Fin d → ℤ)} (hκ : Adm κ) {a₀ : V} (ha₀ : a₀ ∈ M.atoms) (hα : (cls a₀).IsAlpha)
    (hdeg : M.deg a₀ = 2) (hvine : ∃ X j₁ j₂, M.IsVine X M.atoms j₁ j₂) : False := by
  classical
  obtain ⟨ho, hi⟩ := hS.dir2 a₀ ha₀ hdeg
  obtain ⟨x, hx⟩ := card_pos.mp (by unfold Molecule.outdeg at ho; omega : 0 < (((M.dartsAt a₀).filter fun z => M.out z = true)).card)
  obtain ⟨y, hy⟩ := card_pos.mp (by unfold Molecule.indeg at hi; omega : 0 < (((M.dartsAt a₀).filter fun z => M.out z = false)).card)
  simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hx hy
  have hxy : x ≠ y := fun h => by rw [h] at hx; rw [hx.2] at hy; simp at hy
  have hlg := hF.vineLG (Or.inl hvine) κ hκ x y (hx.1.trans hy.1.symm) (by rw [hx.2, hy.2]; simp)
  have hsg := hF.alphaSG κ hκ a₀ ha₀ hα x y hx.1 hy.1 hxy
  exact absurd hlg (not_lt.mpr hsg)

/-- Over the whole atom set, `IsBlock` is a degree statement plus connectivity. -/
theorem isBlock_all (M : Molecule V D) (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    {j₁ j₂ : V} (h1 : j₁ ∈ M.atoms) (h2 : j₂ ∈ M.atoms) (hne : j₁ ≠ j₂)
    (hj1 : M.outdeg j₁ = 1 ∧ M.indeg j₁ = 1) (hj2 : M.outdeg j₂ = 1 ∧ M.indeg j₂ = 1)
    (h4 : ∀ v ∈ M.atoms, v ≠ j₁ → v ≠ j₂ → M.deg v = 4) : M.IsBlock M.atoms j₁ j₂ := by
  classical
  have hIn : ∀ x, M.InGroup M.atoms x := fun x => ⟨M.atom_mem x, M.atom_mem _⟩
  have e1 : ∀ v, M.degIn M.atoms v = M.deg v := fun v => by
    unfold Molecule.degIn Molecule.deg
    congr 1; ext x; simp [hIn x]
  have e2 : ∀ v, M.outIn M.atoms v = M.outdeg v := fun v => by
    unfold Molecule.outIn Molecule.outdeg
    congr 1; ext x; simp [hIn x]
  have e3 : ∀ v, M.inIn M.atoms v = M.indeg v := fun v => by
    unfold Molecule.inIn Molecule.indeg
    congr 1; ext x; simp [hIn x]
  refine ⟨subset_rfl, h1, h2, hne, by rw [e2]; exact hj1.1, by rw [e3]; exact hj1.2,
    by rw [e2]; exact hj2.1, by rw [e3]; exact hj2.2, fun v hv a b => by rw [e1]; exact h4 v hv a b, ?_⟩
  intro u hu v hv
  have key : ∀ a b, M.SameComponent a b →
      Relation.EqvGen (fun a b => ∃ x, M.InGroup M.atoms x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) a b := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨x, hx1, hx2⟩ := hab
      exact Relation.EqvGen.rel _ _ ⟨x, hIn x, hx1, hx2⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact key u v (hconn u hu v hv)

end
end WaveTurbulence.FinalCountG8
