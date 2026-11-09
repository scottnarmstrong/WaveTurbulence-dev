/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproObjMap`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# SUBPRO (S4): transport of vine-like objects and DV's along an induced isomorphism
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem InducedIso.isVC_mapL {B0 : Finset V} {a b : V} (h : Src.IsVC Src.γL N B0 a b) (hB0 : B0 ⊆ B) :
    Src.IsVC Src.γL N' (B0.image I.π) (I.π a) (I.π b) :=
  ⟨(I.restrict hB0).isBlock h.1, by obtain ⟨n, hn⟩ := h.2; exact ⟨n, I.chain_mapL hn hB0⟩⟩

alias _root_.WaveTurbulence.RedSplice.InducedIso.isVC_mapL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.isVC_mapL
theorem InducedIso.isDV_mapL {S : Finset V} {a b : V} (h : Src.IsDV Src.γL N S a b) (hS : S ⊆ B) :
    Src.IsDV Src.γL N' (S.image I.π) (I.π a) (I.π b) := by
  obtain ⟨hσ, A, C, hA, hC, hAC, rfl⟩ := h
  have hAB : A ⊆ B := fun v hv => hS (mem_union_left _ hv)
  have hCB : C ⊆ B := fun v hv => hS (mem_union_right _ hv)
  have hσ' : N'.sigma (I.π a) (I.π b) = 1 := by
    have hab := Src.IsSomeVine.ends hA
    show N'.bondsBetween (I.π a) (I.π b) = 1
    rw [TV.bondsBetween_of_groupBonds_map I.inj I.img.symm I.groupBonds_map a (hAB hab.1) b (hAB hab.2.1)]
    exact hσ
  refine ⟨hσ', A.image I.π, C.image I.π, (I.restrict hAB).isVineS hA, (I.restrict hCB).isVineS hC, ?_,
    Finset.image_union _ _⟩
  rw [← Finset.image_inter_of_injOn A C (I.inj.mono (by
    intro v hv
    rcases hv with hv | hv
    · exact hAB hv
    · exact hCB hv)), hAC]
  simp [Finset.image_insert]

alias _root_.WaveTurbulence.RedSplice.InducedIso.isDV_mapL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.isDV_mapL
/-- Transport of the shape of a vine-like object. -/
@[expose] noncomputable def InducedIso.mapShapeL {A : Finset V} {a b : V} (sh : Src.VineLikeObject Src.γL N A a b)
    (hA : A ⊆ B) : Src.VineLikeObject Src.γL N' (A.image I.π) (I.π a) (I.π b) :=
  match sh with
  | .vc h => .vc (I.isVC_mapL h hA)
  | .hyper R =>
    have he : N.InGroup B R.added :=
      (inGroup_of_ends R.ends_eq (hA R.adjoint.1.2.1) (hA R.adjoint.1.2.2.1))
    .hyper
      { added := (I.e ⟨R.added, he⟩).1
        ends_eq := by rw [I.ends_comm ⟨R.added, he⟩]; show Sym2.map I.π (N.ends R.added) = _; rw [R.ends_eq]; rfl
        adjoint := (I.eraseE R.added he).isVC_mapL R.adjoint hA }

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapShapeL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.mapShapeL
/-- Transport of a vine-like object contained in `B`. -/
@[expose] noncomputable def InducedIso.mapObjL (O : Src.Object Src.γL N) (hO : O.atoms ⊆ B) : Src.Object Src.γL N' :=
  ⟨O.atoms.image I.π, I.π O.upper, I.π O.lower, I.mapShapeL O.shape hO⟩

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapObjL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.mapObjL
theorem InducedIso.mapObj_atomsL (O : Src.Object Src.γL N) (hO : O.atoms ⊆ B) :
    (I.mapObjL O hO).atoms = O.atoms.image I.π := rfl

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_atomsL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.mapObj_atomsL
theorem InducedIso.mapObj_upperL (O : Src.Object Src.γL N) (hO : O.atoms ⊆ B) :
    (I.mapObjL O hO).upper = I.π O.upper := rfl

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_upperL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.mapObj_upperL
theorem InducedIso.mapObj_lowerL (O : Src.Object Src.γL N) (hO : O.atoms ⊆ B) :
    (I.mapObjL O hO).lower = I.π O.lower := rfl

alias _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_lowerL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.mapObj_lowerL
theorem InducedIso.containsDart_mapL (O : Src.Object Src.γL N) (hO : O.atoms ⊆ B) {x : D} (hx : N.InGroup B x) :
    (I.mapObjL O hO).ContainsDart (I.e ⟨x, hx⟩).1 ↔ O.ContainsDart x := by
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

alias _root_.WaveTurbulence.RedSplice.InducedIso.containsDart_mapL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.containsDart_mapL
end WaveTurbulence.GammaLow.FinalCount.H
