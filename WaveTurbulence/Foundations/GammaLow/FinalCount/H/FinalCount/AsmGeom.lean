/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TripleGe4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGeom`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (R48, re-pinned to LG-SPINE AMEND7+8): consumer side of the amended geometry.**
`CountingGeometry` (lg-spine-u, AMEND7) carries `tripleDesignated` and `hingeNoLoop`.  In the REG case (all atoms of degree `≥ 3`, no loops)
G3's standing hypothesis `SubHyp` and `TripleDesig` follow (`subHyp_of_geometry`, `tripleDesig_REG`). -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w d : ℕ}

/-- The asm's dictionary (`collDataOf` of S4-DISJ, restated). -/
def collD {G : Garden w} (C : Src.SubproChoices Src.γL G) : CollData G.molecule :=
  ⟨C.count, C.collection, C.hinges, C.first, C.second⟩

/-- The field gives G3's `TripleDesig3` (S4 form) with no further hypothesis. -/
theorem tripleDesig3_of_field {G : Garden w} (C : Src.SubproChoices Src.γL G) (h : C.TripleDesignated) :
    TripleDesig3 (collD C) := by
  intro a b _ _ _ h3
  obtain ⟨v, hv, c, x, y, hvc, h1, h2, hT, hx, hy⟩ := h a b h3
  exact ⟨v, c, x, y, hvc, hv, h1, h2, hT, hx, hy⟩

/-- ... and G3's `TripleDesig` (the `≥ 4` case is excluded by `SubHyp`, G3 `tripleDesig_of_eq3`). -/
theorem tripleDesig_of_field {R : ℕ} {G : Garden w} (hS : FinalCountG3.SubHyp R G.molecule)
    (C : Src.SubproChoices Src.γL G) (h : C.TripleDesignated) : TripleDesig (collD C) :=
  tripleDesig_of_eq3 hS (tripleDesig3_of_field C h)

/-- REG case: G3's standing hypothesis from the amended geometry. -/
theorem subHyp_of_geometry {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices Src.γL G d}
    (hg : Src.CountingGeometry G C) (hR : 1 ≤ R)
    (h3 : ∀ a ∈ G.molecule.atoms, 3 ≤ G.molecule.deg a)
    (hnl : ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)) :
    FinalCountG3.SubHyp R G.molecule :=
  ⟨hg.molecule.1, h3, by rw [hg.atom_count]; exact hg.bond_count, hnl, hg.connected, hR⟩

theorem tripleDesig_REG {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices Src.γL G d}
    (hg : Src.CountingGeometry G C) (hR : 1 ≤ R)
    (h3 : ∀ a ∈ G.molecule.atoms, 3 ≤ G.molecule.deg a)
    (hnl : ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)) :
    TripleDesig (collD C.subpro) :=
  tripleDesig_of_field (subHyp_of_geometry hg hR h3 hnl) C.subpro hg.tripleDesignated

end WaveTurbulence.GammaLow.FinalCount.H
