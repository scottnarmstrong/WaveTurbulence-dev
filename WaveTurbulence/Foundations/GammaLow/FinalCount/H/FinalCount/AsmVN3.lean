/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 3): the transported object.**  An intact object `U` of `M₀` has a copy `Ũ` in the state
molecule with the same atoms and joints and `Ũ.ContainsDart z ↔ U.ContainsDart (down z)` (`stateObj_spec`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
section pull
variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s) {B : Finset V}
  (hB : ∀ b ∈ B, b ∈ s.M.atoms ∧ s.cls b = .eps)
include hA hD hB

end pull

/-- **The transported object** (`stateIso` + `InducedIso.mapObjL`). -/
theorem stateObj_spec {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (U : Src.Object Src.γL M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) :
    ∃ Ũ : Src.Object Src.γL s.M, Ũ.atoms = U.atoms ∧ Ũ.upper = U.upper ∧ Ũ.lower = U.lower ∧
      (∀ z : s.D, Ũ.ContainsDart z ↔ U.ContainsDart (s.down z)) ∧
      (((∃ h, U.shape = .vc h) → ∃ h, Ũ.shape = .vc h) ∧ ((∃ h, Ũ.shape = .vc h) → ∃ h, U.shape = .vc h)) := by
  let I := stateIso hA hD hint
  refine ⟨I.mapObjL U subset_rfl, (show (U.atoms).image I.π = U.atoms from Finset.image_id), rfl, rfl, fun z => ?_, ?_⟩
  · constructor
    · intro hz
      have hg := containsDart_inGroup _ hz
      have hg' : s.M.InGroup U.atoms z := by
        have hπ : (U.atoms).image I.π = U.atoms := Finset.image_id
        simpa [InducedIso.mapObj_atomsL, hπ] using hg
      have hx := state_group_dart hA hD hint hg'
      have := (I.containsDart_mapL U subset_rfl hx).mp (by
        have e : (I.e ⟨s.down z, hx⟩).1 = z := by
          apply hA.inj
          exact (Classical.choose_spec (group_dart_lift hA hD hint hx)).1
        rw [e]; exact hz)
      exact this
    · intro hz
      have hg := containsDart_inGroup U hz
      have hz' := group_dart_pull hA hD hint hg
      have hx := hg
      have e : (I.e ⟨s.down z, hx⟩).1 = z := by
        apply hA.inj
        exact (Classical.choose_spec (group_dart_lift hA hD hint hx)).1
      have := (I.containsDart_mapL U subset_rfl hx).mpr hz
      rwa [e] at this
  · obtain ⟨S, u, l, sh⟩ := U
    cases sh with
    | vc h => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨h, rfl⟩⟩
    | hyper R => exact ⟨(fun ⟨h, h'⟩ => by cases h'), (fun ⟨h, h'⟩ => by cases h')⟩

end WaveTurbulence.GammaLow.FinalCount.H
