/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapGarden
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 7: the renaming `Sum.inl : V → V ⊕ ℕ`

`inlEmb V` is the embedding `Sum.inl`; `V ⊕ ℕ` is infinite, so G3's run model applies to `mapAtoms M (inlEmb V)`.
All results of parts 1-6 hold for it; the headline specializations are collected here. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp

/-- The renaming `Sum.inl : V → V ⊕ ℕ` as an embedding. -/
def inlEmb (V : Type*) : V ↪ V ⊕ ℕ := ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem inlEmb_apply {V : Type*} (a : V) : inlEmb V a = Sum.inl a := rfl

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The molecule on the infinite atom type `V ⊕ ℕ`. -/
abbrev inlMol (M : Molecule V D) : Molecule (V ⊕ ℕ) D := mapAtoms M (inlEmb V)

theorem inlMol_atoms (M : Molecule V D) : (inlMol M).atoms = M.atoms.map (inlEmb V) := rfl

theorem countA_inl (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P' : Finset (V ⊕ ℕ) → ℝ) :
    (inlMol M).countA L γ δ C₁ w Adm P' = M.countA L γ δ C₁ w Adm (fun S => P' (S.map (inlEmb V))) :=
  mapAtoms_countA M (inlEmb V) L γ δ C₁ w Adm P'

/-- With the ladder scale induced by a scale `P` of `M`: `𝔄` is literally the same quantity. -/
theorem countA_inl_scale (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    (inlMol M).countA L γ δ C₁ w Adm (scaleMap (inlEmb V) P) = M.countA L γ δ C₁ w Adm P := by
  rw [countA_inl]
  simp only [scaleMap_map]

theorem rho_inl (M : Molecule V D) : (inlMol M).rho = M.rho := mapAtoms_rho M (inlEmb V)

theorem isMolecule_inl {M : Molecule V D} (h : M.IsMolecule) : (inlMol M).IsMolecule :=
  mapAtoms_isMolecule M (inlEmb V) h

end WaveTurbulence.AtomTransport
