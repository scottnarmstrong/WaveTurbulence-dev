/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN2
public import WaveTurbulence.Foundations.FinalCount.AsmTransport
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 3): the transported object.**  An intact object `U` of `M₀` has a copy `Ũ` in the state
molecule with the same atoms and joints and `Ũ.ContainsDart z ↔ U.ContainsDart (down z)` (`stateObj_spec`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
section pull
variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s) {B : Finset V}
  (hB : ∀ b ∈ B, b ∈ s.M.atoms ∧ s.cls b = .eps)
include hA hD hB

theorem group_dart_pull {z : s.D} (hz : M₀.InGroup B (s.down z)) : s.M.InGroup B z := by
  have h1 : s.M.atom z = M₀.atom (s.down z) :=
    hA.uniq _ (s.M.atom_mem z) _ (hB _ hz.1).1 (hB _ hz.1).2 (hA.atom z).symm
  have h2 : s.M.atom (s.M.mate z) = M₀.atom (M₀.mate (s.down z)) := by
    have := hA.atom (s.M.mate z)
    rw [← hD.mate] at this
    exact hA.uniq _ (s.M.atom_mem _) _ (hB _ hz.2).1 (hB _ hz.2).2 this.symm
  exact ⟨h1 ▸ hz.1, h2 ▸ hz.2⟩

end pull

/-- **The transported object** (`stateIso` + `InducedIso.mapObj`). -/
theorem stateObj_spec {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (U : Object M₀) (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps) :
    ∃ Ũ : Object s.M, Ũ.atoms = U.atoms ∧ Ũ.upper = U.upper ∧ Ũ.lower = U.lower ∧
      (∀ z : s.D, Ũ.ContainsDart z ↔ U.ContainsDart (s.down z)) ∧
      (((∃ h, U.shape = .vc h) → ∃ h, Ũ.shape = .vc h) ∧ ((∃ h, Ũ.shape = .vc h) → ∃ h, U.shape = .vc h)) := by
  let I := stateIso hA hD hint
  refine ⟨I.mapObj U subset_rfl, (show (U.atoms).image I.π = U.atoms from Finset.image_id), rfl, rfl, fun z => ?_, ?_⟩
  · constructor
    · intro hz
      have hg := containsDart_inGroup _ hz
      have hg' : s.M.InGroup U.atoms z := by
        have hπ : (U.atoms).image I.π = U.atoms := Finset.image_id
        simpa [RedSplice.InducedIso.mapObj_atoms, hπ] using hg
      have hx := state_group_dart hA hD hint hg'
      have := (I.containsDart_map U subset_rfl hx).mp (by
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
      have := (I.containsDart_map U subset_rfl hx).mpr hz
      rwa [e] at this
  · obtain ⟨S, u, l, sh⟩ := U
    cases sh with
    | vc h => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨h, rfl⟩⟩
    | hyper R => exact ⟨(fun ⟨h, h'⟩ => by cases h'), (fun ⟨h, h'⟩ => by cases h')⟩

end WaveTurbulence.FinalCountAsm
