/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceInduced
public import WaveTurbulence.Foundations.FinalCount.S1Basic
import Mathlib.Tactic

/-!
# SUBPRO (S4): induced isomorphisms, restriction, and transport of vines, chains, VC's and DV's
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']

namespace InducedIso
variable {M : Molecule V D} {M' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso M M' B B')

theorem img_sub {T : Finset V} (hT : T ⊆ B) : T.image I.π ⊆ B' := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
  exact I.pi_mem (hT hu)

theorem inGroup_img {T : Finset V} (hT : T ⊆ B) (x : D) (hx : M.InGroup T x) :
    M'.InGroup (T.image I.π) (I.e ⟨x, ⟨hT hx.1, hT hx.2⟩⟩).1 := by
  have hxB : M.InGroup B x := ⟨hT hx.1, hT hx.2⟩
  constructor
  · rw [I.atom_comm ⟨x, hxB⟩]; exact Finset.mem_image_of_mem _ hx.1
  · rw [← I.mate_comm ⟨x, hxB⟩, I.atom_comm]; exact Finset.mem_image_of_mem _ hx.2

theorem inGroup_pre {T : Finset V} (hT : T ⊆ B) (y : D') (hy : M'.InGroup (T.image I.π) y) :
    M.InGroup T (I.e.symm ⟨y, ⟨I.img_sub hT hy.1, I.img_sub hT hy.2⟩⟩).1 := by
  set x := I.e.symm ⟨y, ⟨I.img_sub hT hy.1, I.img_sub hT hy.2⟩⟩ with hx
  have hxe : I.e x = ⟨y, ⟨I.img_sub hT hy.1, I.img_sub hT hy.2⟩⟩ := by rw [hx]; exact Equiv.apply_symm_apply _ _
  have h1 : M'.atom y = I.π (M.atom x.1) := by
    have := I.atom_comm x
    rw [hxe] at this; exact this
  have h2 : M'.atom (M'.mate y) = I.π (M.atom (M.mate x.1)) := by
    have := I.mate_comm x
    rw [hxe] at this
    rw [← this, I.atom_comm]
  constructor
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp (h1 ▸ hy.1 : I.π (M.atom x.1) ∈ T.image I.π)
    have : t = M.atom x.1 := I.inj (hT ht) x.2.1 hte
    exact this ▸ ht
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp (h2 ▸ hy.2 : I.π (M.atom (M.mate x.1)) ∈ T.image I.π)
    have : t = M.atom (M.mate x.1) := I.inj (hT ht) x.2.2 hte
    exact this ▸ ht

/-- Restriction of an induced isomorphism to a subset. -/
@[expose] noncomputable def restrict {T : Finset V} (hT : T ⊆ B) : InducedIso M M' T (T.image I.π) where
  π := I.π
  inj := I.inj.mono (by simpa using hT)
  img := rfl
  sub := fun v hv => I.sub (I.img_sub hT hv)
  e :=
    { toFun := fun x => ⟨(I.e ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩).1, I.inGroup_img hT x.1 x.2⟩
      invFun := fun y => ⟨(I.e.symm ⟨y.1, ⟨I.img_sub hT y.2.1, I.img_sub hT y.2.2⟩⟩).1, I.inGroup_pre hT y.1 y.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (I.e.symm ⟨(I.e ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩).1, _⟩).1 = x.1
        rw [show (⟨(I.e ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩).1, _⟩ : {y : D' // M'.InGroup B' y}) =
          I.e ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩ from Subtype.ext rfl, Equiv.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        show (I.e ⟨(I.e.symm ⟨y.1, ⟨I.img_sub hT y.2.1, I.img_sub hT y.2.2⟩⟩).1, _⟩).1 = y.1
        rw [show (⟨(I.e.symm ⟨y.1, ⟨I.img_sub hT y.2.1, I.img_sub hT y.2.2⟩⟩).1, _⟩ : {x : D // M.InGroup B x}) =
          I.e.symm ⟨y.1, ⟨I.img_sub hT y.2.1, I.img_sub hT y.2.2⟩⟩ from Subtype.ext rfl, Equiv.apply_symm_apply] }
  atom_comm := fun x => I.atom_comm ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩
  mate_comm := fun x => I.mate_comm ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩
  out_comm := fun x => I.out_comm ⟨x.1, ⟨hT x.2.1, hT x.2.2⟩⟩

end InducedIso

end WaveTurbulence.RedSplice
