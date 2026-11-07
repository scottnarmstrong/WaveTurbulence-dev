/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGarden3
public import WaveTurbulence.Foundations.FinalCount.AtMapCount
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
/-! **FINALCOUNT-ASSEMBLY (garden level, 4): decorations of the renamed molecule at base `0`.**  For `κ = bondIndex z` with `z` a
`GenDecoration G d roots 0`: `κ` is a `c₀`-decoration of `inlMol G.molecule` with `c₀ = gardenSource …` (fixed by the roots) and
`c₀ = 0` at degree-`4` atoms.  Consequences: `hdec`, `h0`, `PinnedM0` of the class theorem. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCount WaveTurbulence.AtomTransport WaveTurbulence.MoleProp
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole

variable {R d : ℕ}

/-- The charge function of the class: fixed by the roots. -/
noncomputable def gardenCharge (G : Garden (2 * R)) (hp : G.IsPlain) (L : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ)) :
    (GBranch G.tree ⊕ ℕ) → Mom d :=
  Sum.elim (gardenSource G hp (fun i => (0 : Mom d) + latticePoint L (roots i))) (fun _ => 0)

theorem garden_decoration_inl (G : Garden (2 * R)) (hp : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) :
    (inlMol G.molecule).IsDecoration L (0 : Mom d) (gardenCharge G hp L roots) (bondIndex G z.1) ∧
      ∀ x ∈ (inlMol G.molecule).atoms, (inlMol G.molecule).deg x = 4 → gardenCharge G hp L roots x = 0 := by
  constructor
  · have h := spliced_molecule_decoration G hp hL (0 : Mom d) roots z
    exact (mapAtoms_isDecoration G.molecule (inlEmb _) L 0 _ _).2 (by simpa [gardenCharge, Function.comp_def] using h)
  · intro x hx hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    have hd' : G.molecule.deg a = 4 := by
      rw [← mapAtoms_deg G.molecule (inlEmb (GBranch G.tree)) a]; exact hd
    show Sum.elim _ _ (Sum.inl a) = 0
    simp only [Sum.elim_inl]
    exact gardenSource_eq_zero_of_deg_four G hp _ a hd'


theorem class_dec_facts (G : Garden (2 * R)) (hp : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (roots : Fin (2 * R) → (Fin d → ℤ))
    {A0 : Set (GardenDart G → (Fin d → ℤ))} (hz : ∀ κ ∈ A0, ∃ z : GenDecoration G d roots 0, ∀ x, bondIndex G z.1 x = κ x) :
    (∀ k ∈ A0, ∃ c0, (inlMol G.molecule).IsDecoration L (0 : Mom d) c0 k ∧
      ∀ x ∈ (inlMol G.molecule).atoms, (inlMol G.molecule).deg x = 4 → c0 x = 0) ∧
    (∀ κ ∈ A0, ∀ a ∈ (inlMol G.molecule).atoms, (inlMol G.molecule).deg a = 4 →
      ∑ x ∈ (inlMol G.molecule).dartsAt a, (inlMol G.molecule).dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) ∧
    PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) (inlMol G.molecule) := by
  have key : ∀ κ ∈ A0, (inlMol G.molecule).IsDecoration L (0 : Mom d) (gardenCharge G hp L roots) κ ∧
      ∀ x ∈ (inlMol G.molecule).atoms, (inlMol G.molecule).deg x = 4 → gardenCharge G hp L roots x = 0 := by
    intro κ hκ
    obtain ⟨z, hz⟩ := hz κ hκ
    have e : bondIndex G z.1 = κ := funext hz
    rw [← e]
    exact garden_decoration_inl G hp hL roots z
  refine ⟨fun k hk => ⟨_, (key k hk).1, (key k hk).2⟩, ?_, ?_⟩
  · intro κ hκ a ha h4
    rw [(key κ hκ).1.2 a ha]
    exact (key κ hκ).2 a ha h4
  · intro a ha
    refine ⟨gardenCharge G hp L roots a, fun k0 hk0 => ?_⟩
    exact (key k0 hk0).1.2 a ha

end WaveTurbulence.FinalCountAsm
