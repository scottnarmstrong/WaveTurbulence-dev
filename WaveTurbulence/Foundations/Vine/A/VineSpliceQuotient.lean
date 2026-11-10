/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIter
public import WaveTurbulence.Foundations.Molecule.BoundaryAddressAlgebra
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso
/-! VINE-A4 fallback infrastructure: two actual splice maps with identical
merge classes have canonically isomorphic quotient molecules, using old names. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1

/-- An injective carrier is canonically identified with another copy of the same range. -/
noncomputable def equivOfSameRange {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : ∀ x, (∃ a, f a = x) ↔ ∃ b, g b = x) : A ≃ B := by
  let F : A → B := fun a => ((hr (f a)).mp ⟨a, rfl⟩).choose
  let J : B → A := fun b => ((hr (g b)).mpr ⟨b, rfl⟩).choose
  have hF : ∀ a, g (F a) = f a := fun a => ((hr (f a)).mp ⟨a, rfl⟩).choose_spec
  have hJ : ∀ b, f (J b) = g b := fun b => ((hr (g b)).mpr ⟨b, rfl⟩).choose_spec
  exact ⟨F, J, fun a => hf ((hJ (F a)).trans (hF a)), fun b => hg ((hF (J b)).trans (hJ b))⟩

theorem equivOfSameRange_comm {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : ∀ x, (∃ a, f a = x) ↔ ∃ b, g b = x) (a : A) :
    g (equivOfSameRange f g hf hg hr a) = f a := ((hr (f a)).mp ⟨a, rfl⟩).choose_spec

variable {w : ℕ} {G H K : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}

end WaveTurbulence.VineA
