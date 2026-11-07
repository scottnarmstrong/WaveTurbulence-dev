/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
/-! **FINALCOUNT-ASSEMBLY (E3): transport of an intact group to the state.**  For a set `B` of present `ε`-atoms of a state `s` with
`AncRel`/`DartRel`, `down` restricts to an isomorphism of the induced groups of `M₀` and of `s.M` (`stateIso`, identity on atoms).
So `InducedIso.mapObj` (S4's `SubproObjMap`) transports collected objects to the current molecule. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

section iso
variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s) {B : Finset V}
  (hB : ∀ b ∈ B, b ∈ s.M.atoms ∧ s.cls b = .eps)
include hA hD hB

theorem state_group_dart {y : s.D} (hy : s.M.InGroup B y) : M₀.InGroup B (s.down y) := by
  refine ⟨?_, ?_⟩
  · rw [hD.eps y (hB _ hy.1).2]
    exact hy.1
  · rw [hD.mate, hD.eps _ (hB _ hy.2).2]
    exact hy.2

theorem group_dart_lift {z : D₀} (hz : M₀.InGroup B z) : ∃ y : s.D, s.down y = z ∧ s.M.InGroup B y := by
  obtain ⟨y, hy⟩ := hA.surj _ (hB _ hz.1).1 (hB _ hz.1).2 z rfl
  have h1 : s.M.atom y = M₀.atom z := by
    have := hA.atom y
    rw [hy] at this
    exact hA.uniq _ (s.M.atom_mem y) _ (hB _ hz.1).1 (hB _ hz.1).2 this.symm
  have h2 : s.M.atom (s.M.mate y) = M₀.atom (M₀.mate z) := by
    have := hA.atom (s.M.mate y)
    rw [← hD.mate, hy] at this
    exact hA.uniq _ (s.M.atom_mem _) _ (hB _ hz.2).1 (hB _ hz.2).2 this.symm
  exact ⟨y, hy, h1 ▸ hz.1, h2 ▸ hz.2⟩

/-- The identity-on-atoms induced isomorphism between `M₀` and the state, on a group of intact atoms. -/
noncomputable def stateIso : RedSplice.InducedIso M₀ s.M B B where
  π := id
  inj := Set.injOn_id _
  img := Finset.image_id
  sub := fun b hb => (hB b hb).1
  e :=
    { toFun := fun x => ⟨Classical.choose (group_dart_lift hA hD hB x.2), (Classical.choose_spec (group_dart_lift hA hD hB x.2)).2⟩
      invFun := fun y => ⟨s.down y.1, state_group_dart hA hD hB y.2⟩
      left_inv := fun x => Subtype.ext (Classical.choose_spec (group_dart_lift hA hD hB x.2)).1
      right_inv := fun y => Subtype.ext (hA.inj (Classical.choose_spec (group_dart_lift hA hD hB (state_group_dart hA hD hB y.2))).1) }
  atom_comm := fun x => by
    have := Classical.choose_spec (group_dart_lift hA hD hB x.2)
    show s.M.atom (Classical.choose (group_dart_lift hA hD hB x.2)) = M₀.atom x.1
    have h3 := hD.eps _ (hB _ this.2.1).2
    rw [this.1] at h3
    exact h3.symm
  mate_comm := fun x => by
    have hx := Classical.choose_spec (group_dart_lift hA hD hB x.2)
    have hm := Classical.choose_spec (group_dart_lift hA hD hB
      (show M₀.InGroup B (M₀.mate x.1) from ⟨x.2.2, by simpa [M₀.mate_mate] using x.2.1⟩))
    have e2 : s.down (s.M.mate (Classical.choose (group_dart_lift hA hD hB x.2))) = M₀.mate x.1 := by
      rw [← hD.mate, hx.1]
    exact hA.inj (hm.1.trans e2.symm)
  out_comm := fun x => by
    have hx := Classical.choose_spec (group_dart_lift hA hD hB x.2)
    show s.M.out (Classical.choose (group_dart_lift hA hD hB x.2)) = M₀.out x.1
    rw [← hD.out, hx.1]

end iso

end WaveTurbulence.FinalCountAsm
