/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
/-! # SUBPRO (S4) over `𝒱_γ`: transport of vine-like objects and `DV′` along an induced isomorphism (packet L5c, E)

L5c port of main `WaveTurbulence.Foundations.FinalCount.SubproObjMap` (sha256 in COPIED-SHA256SUMS): the declarations
that depend on the vine family, over L6's carrier `Src … γ` (`γ ≤ 1/2`). Main's family-free `inGroup_of_ends`,
`InducedIso.eraseE`, `InducedIso.inGroup_map_iff` are used by import. Members of `𝒱_γ` are transported by L5a's
`Fama.isSomeVine_iso` (T-vines: `TVineIsoInvariant`, proved), chains by L5a's `Fama.InducedIso.chain_map`, and the
`σ = 1` clause of `DV′` (`Molecule.IsDVPrime`) by L5a's `Fama.IsoMol.bondsBetween_eq`.

The declarations are named `InducedIso.<main name>Fc` in main's namespace `WaveTurbulence.RedSplice` so that main's dot
notation (`I.isVC_map …`) ports as `I.isVC_mapFc …`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Stage1

variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq V'] [Fintype D'] [DecidableEq D']
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

/-- A VC of `𝒱_γ` inside `B` is carried to a VC (main `InducedIso.isVC_map`). -/
theorem _root_.WaveTurbulence.RedSplice.InducedIso.isVC_mapFc {B0 : Finset V} {a b : V} (h : Src.IsVC γ N B0 a b)
    (hB0 : B0 ⊆ B) : Src.IsVC γ N' (B0.image I.π) (I.π a) (I.π b) :=
  ⟨(I.restrict hB0).isBlock h.1, by obtain ⟨n, hn⟩ := h.2; exact ⟨n, Fama.InducedIso.chain_map I hn hB0⟩⟩

/-- A `DV′` inside `B` is carried to a `DV′` (main `InducedIso.isDV_map`; the `σ = 1` clause by
`IsoMol.bondsBetween_eq`). -/
theorem _root_.WaveTurbulence.RedSplice.InducedIso.isDV_mapFc {S : Finset V} {a b : V} (h : Src.IsDV γ N S a b)
    (hS : S ⊆ B) : Src.IsDV γ N' (S.image I.π) (I.π a) (I.π b) := by
  obtain ⟨hσ, A, C, hA, hC, hAC, rfl⟩ := h
  have hAB : A ⊆ B := fun v hv => hS (mem_union_left _ hv)
  have hCB : C ⊆ B := fun v hv => hS (mem_union_right _ hv)
  have haA : a ∈ A := (Src.isBlock_of_isSomeVine hA).2.1
  have hbA : b ∈ A := (Src.isBlock_of_isSomeVine hA).2.2.1
  refine ⟨?_, A.image I.π, C.image I.π, isSomeVine_iso (I.restrict hAB) hA, isSomeVine_iso (I.restrict hCB) hC, ?_,
    Finset.image_union _ _⟩
  · show N'.bondsBetween (I.π a) (I.π b) = 1
    rw [IsoMol.bondsBetween_eq I (hAB haA) (hAB hbA)]; exact hσ
  · rw [← Finset.image_inter_of_injOn A C (I.inj.mono (by
      intro v hv
      rcases hv with hv | hv
      · exact hAB hv
      · exact hCB hv)), hAC]
    simp [Finset.image_insert]

/-- Transport of the shape of a vine-like object (main `InducedIso.mapShape`). -/
@[expose] noncomputable def _root_.WaveTurbulence.RedSplice.InducedIso.mapShapeFc {A : Finset V} {a b : V}
    (sh : Src.VineLikeObject γ N A a b) (hA : A ⊆ B) : Src.VineLikeObject γ N' (A.image I.π) (I.π a) (I.π b) :=
  match sh with
  | .vc h => .vc (I.isVC_mapFc h hA)
  | .hyper R =>
    have he : N.InGroup B R.added :=
      (inGroup_of_ends R.ends_eq (hA R.adjoint.1.2.1) (hA R.adjoint.1.2.2.1))
    .hyper
      { added := (I.e ⟨R.added, he⟩).1
        ends_eq := by rw [I.ends_comm ⟨R.added, he⟩]; show Sym2.map I.π (N.ends R.added) = _; rw [R.ends_eq]; rfl
        adjoint := (I.eraseE R.added he).isVC_mapFc R.adjoint hA }

/-- Transport of a vine-like object contained in `B` (main `InducedIso.mapObj`). -/
@[expose] noncomputable def _root_.WaveTurbulence.RedSplice.InducedIso.mapObjFc (O : Src.Object γ N)
    (hO : O.atoms ⊆ B) : Src.Object γ N' :=
  ⟨O.atoms.image I.π, I.π O.upper, I.π O.lower, I.mapShapeFc O.shape hO⟩

theorem _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_atomsFc (O : Src.Object γ N) (hO : O.atoms ⊆ B) :
    (I.mapObjFc O hO).atoms = O.atoms.image I.π := rfl

theorem _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_upperFc (O : Src.Object γ N) (hO : O.atoms ⊆ B) :
    (I.mapObjFc O hO).upper = I.π O.upper := rfl

theorem _root_.WaveTurbulence.RedSplice.InducedIso.mapObj_lowerFc (O : Src.Object γ N) (hO : O.atoms ⊆ B) :
    (I.mapObjFc O hO).lower = I.π O.lower := rfl

/-- A dart of `B` is in the transported object iff it is in the object (main `InducedIso.containsDart_map`). -/
theorem _root_.WaveTurbulence.RedSplice.InducedIso.containsDart_mapFc (O : Src.Object γ N) (hO : O.atoms ⊆ B) {x : D}
    (hx : N.InGroup B x) : (I.mapObjFc O hO).ContainsDart (I.e ⟨x, hx⟩).1 ↔ O.ContainsDart x := by
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

end WaveTurbulence.GammaLow.Famc.Subpro
