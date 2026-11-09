/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineF`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: a vine removal never decreases the number of components** (so the `α`-case `F_pos ≤ F_pre` of Step 1
is `ΔF = 0`, DH23 L1798): the collapse `fa ↦ upper, fb ↦ lower` is a surjection of the component sets of `K.post` onto
those of `M`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem vine_F_ge {M : Molecule V D} (K : Step1.VineCut Src.γL M) : M.numComponents ≤ K.post.numComponents := by
  have hfa : K.fa ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
  let f : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) → Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Quot.map (fun a : K.post.atoms => (⟨piVine K a.1, piVine_mem K a.2⟩ : M.atoms)) (by
      intro a b h
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z.1, ?_, ?_⟩
      · show M.atom z.1 = piVine K a.1
        rw [← hz1]; exact (piVine_atom K z.1).symm
      · show M.atom (M.mate z.1) = piVine K b.1
        rw [← hz2]; exact (piVine_atom K (K.cutMol.mate z.1)).symm)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quot.ind with
    | mk a =>
      obtain ⟨a, ha⟩ := a
      by_cases hC : a ∈ K.C.atoms
      · refine ⟨Quot.mk _ ⟨K.fa, hfa⟩, ?_⟩
        show Quot.mk _ (⟨piVine K K.fa, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        rw [quot_mk_eq_iff M _ _ _ ha]
        have : piVine K K.fa = K.C.upper := by simp [piVine]
        rw [this]
        exact vine_obj_sc K K.a_mem hC
      · have hp : a ∈ K.post.atoms := by
          rw [post_atoms_eq, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha), hC⟩
        refine ⟨Quot.mk _ ⟨a, hp⟩, ?_⟩
        show Quot.mk _ (⟨piVine K a, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        have h1 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ ha)
        have h2 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ ha)
        simp only [piVine, h1, h2, if_false]
  exact Nat.card_le_card_of_surjective f hsurj

theorem vine_F_alpha_iff {M : Molecule V D} (K : Step1.VineCut Src.γL M) :
    K.post.numComponents ≤ M.numComponents ↔ K.post.numComponents = M.numComponents :=
  ⟨fun h => le_antisymm h (vine_F_ge K), le_of_eq⟩

end WaveTurbulence.GammaLow.FinalCount.H
