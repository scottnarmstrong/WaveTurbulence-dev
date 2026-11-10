/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproIso2
import Mathlib.Tactic

/-!
# SUBPRO (S4): transport of vine-like objects and DV's along an induced isomorphism
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem inGroup_of_ends {M : Molecule V D} {e : D} {A : Finset V} {a b : V} (h : M.ends e = s(a, b))
    (ha : a ∈ A) (hb : b ∈ A) : M.InGroup A e := by
  unfold Molecule.ends at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ ha, h2 ▸ hb⟩
  · exact ⟨h1 ▸ hb, h2 ▸ ha⟩

/-- `InducedIso.erase`, exposed (with the same `π`). -/
@[expose] noncomputable def InducedIso.eraseE (e : D) (he : N.InGroup B e) :
    InducedIso (N.eraseBond e) (N'.eraseBond (I.e ⟨e, he⟩).1) B B' where
  π := I.π
  inj := I.inj
  img := I.img
  sub := I.sub
  e :=
    { toFun := fun x =>
        ⟨⟨(I.e ⟨x.1.1, x.2⟩).1,
          fun h => x.1.2.1 ((I.e_eq_iff he ⟨x.1.1, x.2⟩).mp h),
          fun h => x.1.2.2 ((I.e_mate_iff he ⟨x.1.1, x.2⟩).mp h)⟩, (I.e ⟨x.1.1, x.2⟩).2⟩
      invFun := fun y =>
        ⟨⟨(I.e.symm ⟨y.1.1, y.2⟩).1,
          fun h => y.1.2.1 (by
            have := (I.e_eq_iff he (I.e.symm ⟨y.1.1, y.2⟩)).mpr h
            simpa using this),
          fun h => y.1.2.2 (by
            have := (I.e_mate_iff he (I.e.symm ⟨y.1.1, y.2⟩)).mpr h
            simpa using this)⟩, (I.e.symm ⟨y.1.1, y.2⟩).2⟩
      left_inv := fun x =>
        Subtype.ext (Subtype.ext (by
          have h := congrArg Subtype.val (I.e.symm_apply_apply ⟨x.1.1, x.2⟩)
          exact h))
      right_inv := fun y =>
        Subtype.ext (Subtype.ext (by
          have h := congrArg Subtype.val (I.e.apply_symm_apply ⟨y.1.1, y.2⟩)
          exact h)) }
  atom_comm := fun x => I.atom_comm ⟨x.1.1, x.2⟩
  mate_comm := fun x => by
    have := I.mate_comm ⟨x.1.1, x.2⟩
    exact Subtype.ext this
  out_comm := fun x => I.out_comm ⟨x.1.1, x.2⟩

theorem InducedIso.isVC_map {B0 : Finset V} {a b : V} (h : IsVC N B0 a b) (hB0 : B0 ⊆ B) :
    IsVC N' (B0.image I.π) (I.π a) (I.π b) :=
  ⟨(I.restrict hB0).isBlock h.1, by obtain ⟨n, hn⟩ := h.2; exact ⟨n, I.chain_map hn hB0⟩⟩

theorem InducedIso.isDV_map {S : Finset V} {a b : V} (h : IsDV N S a b) (hS : S ⊆ B) :
    IsDV N' (S.image I.π) (I.π a) (I.π b) := by
  obtain ⟨A, C, hA, hC, hAC, rfl⟩ := h
  have hAB : A ⊆ B := fun v hv => hS (mem_union_left _ hv)
  have hCB : C ⊆ B := fun v hv => hS (mem_union_right _ hv)
  refine ⟨A.image I.π, C.image I.π, (I.restrict hAB).isVine hA, (I.restrict hCB).isVine hC, ?_, Finset.image_union _ _⟩
  rw [← Finset.image_inter_of_injOn A C (I.inj.mono (by
    intro v hv
    rcases hv with hv | hv
    · exact hAB hv
    · exact hCB hv)), hAC]
  simp [Finset.image_insert]

/-- Transport of the shape of a vine-like object. -/
@[expose] noncomputable def InducedIso.mapShape {A : Finset V} {a b : V} (sh : VineLikeObject N A a b)
    (hA : A ⊆ B) : VineLikeObject N' (A.image I.π) (I.π a) (I.π b) :=
  match sh with
  | .vc h => .vc (I.isVC_map h hA)
  | .hyper R =>
    have he : N.InGroup B R.added :=
      (inGroup_of_ends R.ends_eq (hA R.adjoint.1.2.1) (hA R.adjoint.1.2.2.1))
    .hyper
      { added := (I.e ⟨R.added, he⟩).1
        ends_eq := by rw [I.ends_comm ⟨R.added, he⟩]; show Sym2.map I.π (N.ends R.added) = _; rw [R.ends_eq]; rfl
        adjoint := (I.eraseE R.added he).isVC_map R.adjoint hA }

/-- Transport of a vine-like object contained in `B`. -/
@[expose] noncomputable def InducedIso.mapObj (O : Object N) (hO : O.atoms ⊆ B) : Object N' :=
  ⟨O.atoms.image I.π, I.π O.upper, I.π O.lower, I.mapShape O.shape hO⟩

theorem InducedIso.mapObj_atoms (O : Object N) (hO : O.atoms ⊆ B) :
    (I.mapObj O hO).atoms = O.atoms.image I.π := rfl

theorem InducedIso.mapObj_upper (O : Object N) (hO : O.atoms ⊆ B) :
    (I.mapObj O hO).upper = I.π O.upper := rfl

theorem InducedIso.inGroup_map_iff {A : Finset V} (hA : A ⊆ B) {x : D} (hx : N.InGroup B x) :
    N'.InGroup (A.image I.π) (I.e ⟨x, hx⟩).1 ↔ N.InGroup A x := by
  constructor
  · intro hy
    have := I.inGroup_pre hA _ hy
    have e : I.e.symm ⟨(I.e ⟨x, hx⟩).1, ⟨I.img_sub hA hy.1, I.img_sub hA hy.2⟩⟩ = ⟨x, hx⟩ := by
      rw [show (⟨(I.e ⟨x, hx⟩).1, ⟨I.img_sub hA hy.1, I.img_sub hA hy.2⟩⟩ : {y : D' // N'.InGroup B' y}) =
        I.e ⟨x, hx⟩ from rfl]
      exact Equiv.symm_apply_apply _ _
    rw [e] at this; exact this
  · intro hx'
    exact I.inGroup_img hA x hx'

theorem InducedIso.containsDart_map (O : Object N) (hO : O.atoms ⊆ B) {x : D} (hx : N.InGroup B x) :
    (I.mapObj O hO).ContainsDart (I.e ⟨x, hx⟩).1 ↔ O.ContainsDart x := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc h => exact I.inGroup_map_iff hO hx
  | hyper R =>
    have he : N.InGroup B R.added := inGroup_of_ends R.ends_eq (hO R.adjoint.1.2.1) (hO R.adjoint.1.2.2.1)
    show ((I.e ⟨x, hx⟩).1 ≠ (I.e ⟨R.added, he⟩).1 ∧ (I.e ⟨x, hx⟩).1 ≠ N'.mate (I.e ⟨R.added, he⟩).1 ∧
      N'.InGroup (A.image I.π) (I.e ⟨x, hx⟩).1) ↔ (x ≠ R.added ∧ x ≠ N.mate R.added ∧ N.InGroup A x)
    rw [I.inGroup_map_iff hO hx]
    have h1 := I.e_eq_iff he ⟨x, hx⟩
    have h2 := I.e_mate_iff he ⟨x, hx⟩
    simp only [] at h1 h2
    constructor
    · rintro ⟨a1, a2, a3⟩
      exact ⟨fun h => a1 (h1.mpr h), fun h => a2 (h2.mpr h), a3⟩
    · rintro ⟨a1, a2, a3⟩
      exact ⟨fun h => a1 (h1.mp h), fun h => a2 (h2.mp h), a3⟩

end WaveTurbulence.RedSplice
