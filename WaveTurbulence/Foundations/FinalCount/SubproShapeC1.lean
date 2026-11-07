/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
import Mathlib.Tactic

/-!
# S4-SHAPE goal 1: every object of `C₁` is single-vine classified (`hC1vine`)

TARGET `subpro` (2) (L2043): each object of `C₁` is an SG HV, an SG (CN) vine or an SG root (CL) vine. S2a's construction records
this as `AllowedCollectionObject` (`ObjSpec.allowed`, `structural_collectionChoices`): a vc-shaped object is `IsSomeVine` in the
molecule, a hyper-shaped one is `IsSomeVine` in the adjoint of its designated bond. That is exactly the assembly's `ObjVine`.
A vine has at least four atoms, so the `U.atoms.card = 3` branch of the assembly's shape hypothesis never occurs for `C₁`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountAsm

variable {w : ℕ}

/-- An allowed collection object (TARGET `subpro` (2)) is `ObjVine` at the molecule of its garden. -/
theorem objVine_of_allowed {G : Garden w} {U : Object G.molecule} (h : AllowedCollectionObject G U) :
    ObjVine G.molecule U := by
  unfold ObjVine
  unfold AllowedCollectionObject at h
  rcases hs : U.shape with h0 | R
  · rw [hs] at h
    obtain ⟨X, hX⟩ := h.1
    exact ⟨X, hX⟩
  · rw [hs] at h
    obtain ⟨X, hX⟩ := h
    exact ⟨X, hX⟩

/-- **`hC1vine`.** Every object of the first collection `C₁` of `collectionChoices G σ` is `ObjVine` at `M₀ = G_sb.molecule`. -/
theorem c1_objVine {G : Garden w} (hM : G.molecule.IsMolecule) (σ : RedSplice.Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) (i : Fin (RedSplice.collectionChoices G σ).count) :
    ObjVine (RedSplice.stSt G σ).G.molecule ((RedSplice.collectionChoices G σ).collection i) :=
  objVine_of_allowed ((RedSplice.structural_collectionChoices hM σ hno).1 i)

/-- A vine has at least four atoms or is a double bond (two atoms): an object classified by `ObjVine` never has exactly three atoms. -/
theorem objVine_card_ne_three {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀]
    {M : Molecule V D₀} {U : Object M} (h : ObjVine M U) : U.atoms.card ≠ 3 := by
  intro h3
  unfold ObjVine at h
  rcases hs : U.shape with h0 | R
  · rw [hs] at h
    obtain ⟨X, hX⟩ := h
    have := Vine.isVine_typeI_of_card_lt_four hX (by omega)
    subst this
    have := Vine.typeI_atoms hX
    rw [this, Finset.card_pair hX.1.2.2.2.1] at h3
    omega
  · rw [hs] at h
    obtain ⟨X, hX⟩ := h
    have := Vine.isVine_typeI_of_card_lt_four hX (by omega)
    subst this
    have := Vine.typeI_atoms hX
    rw [this, Finset.card_pair hX.1.2.2.2.1] at h3
    omega

/-- **`hC1vine`, in the form `vhard_of_shape` consumes.** -/
theorem c1_shape {G : Garden w} (hM : G.molecule.IsMolecule) (σ : RedSplice.Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) (i : Fin (RedSplice.collectionChoices G σ).count) :
    ((RedSplice.collectionChoices G σ).collection i).atoms.card = 3 ∨
      ObjVine (RedSplice.stSt G σ).G.molecule ((RedSplice.collectionChoices G σ).collection i) :=
  Or.inr (c1_objVine hM σ hno i)

end WaveTurbulence.Subpro
