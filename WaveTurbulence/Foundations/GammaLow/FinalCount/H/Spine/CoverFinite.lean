/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverAdmissible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.CoverFinite`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The finite cover index, its geometry and its weight budget (TARGET L2088, L2097-L2116),
over arbitrary subpro choice data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.Cover
open WaveTurbulence.Induct
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Set Finset
open scoped Classical

variable {d : ℕ}

/-- The finite index of occurring counting choices of the spliced kernel. -/
def CoverIndex {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (D : SplicedKernelData G d)
    (Cs : Src.SubproChoices Src.γL G) (L γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) :=
  {j : (t : Tag G) × Scales (tagChoice G hM Cs L γ η base roots t) L γ η //
    ∃ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 ∧
      (fullChoice (tagChoice G hM Cs L γ η base roots j.1) j.2).Admissible L γ η base
        (bondIndex G z.1)}

noncomputable def CoverIndex.choice {R : ℕ} {G : Garden (2 * R)} {hM : G.molecule.IsMolecule}
    {D : SplicedKernelData G d} {Cs : Src.SubproChoices Src.γL G} {L γ η : ℝ} {base : Mom d}
    {roots : Fin (2 * R) → (Fin d → ℤ)} (j : CoverIndex G hM D Cs L γ η base roots) :
    Src.CountingChoices Src.γL G d :=
  fullChoice (tagChoice G hM Cs L γ η base roots j.1.1) j.1.2

theorem finite_scales {w : ℕ} {G : Garden w} (B : Src.CountingChoices Src.γL G d) {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) : Finite (Scales B L γ η) := by
  have := finite_sourcePositiveLadderScale hL
  have : Finite (AtomScale L γ η) :=
    Finite.of_injective
      (fun P : AtomScale L γ η => (⟨P.1, P.2.1, P.2.2.1, P.2.2.2.trans hb⟩ : SourcePositiveLadderScale L))
      (fun P Q h => Subtype.ext (by simpa using congrArg Subtype.val h))
  unfold Scales LadderChoices
  infer_instance

theorem finite_coverIndex {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule)
    (D : SplicedKernelData G d) (Cs : Src.SubproChoices Src.γL G) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (hb : L ^ (-γ + η) ≤ 1) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) :
    Finite (CoverIndex G hM D Cs L γ η base roots) := by
  have : ∀ t : Tag G, Finite (Scales (tagChoice G hM Cs L γ η base roots t) L γ η) :=
    fun t => finite_scales _ hL γ η hb
  have : Finite (Tag G) := inferInstance
  have : Finite ((t : Tag G) × Scales (tagChoice G hM Cs L γ η base roots t) L γ η) :=
    inferInstance
  unfold CoverIndex
  infer_instance

/-- Geometry of every occurring choice: subpro (1),(2), the hinge assertions of TARGET L2116
(C1 half is a hypothesis, C2 half is derived), and the hinge SG labels. -/
theorem coverIndex_geometry_of_subpro_choices {R : ℕ} (G : Garden (2 * R))
    (hM : G.molecule.IsMolecule) (hconn : G.molecule.IsConnected)
    (hatoms : G.molecule.atoms.card = G.order) (hbonds : G.molecule.bonds.card + R = 2 * G.order)
    (D : SplicedKernelData G d)
    (Cs : Src.SubproChoices Src.γL G) {L : ℝ} (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (hS : SubproConclusions G D Cs L γ η base roots)
    (j : CoverIndex G hM D Cs L γ η base roots) :
    Src.CountingGeometry G j.choice := by
  obtain ⟨z, hz, hadm⟩ := j.2
  have hadm' : (CoverIndex.choice j).Admissible L γ η base (bondIndex G z.1) := hadm
  obtain ⟨hsub, hsec, hlab, _⟩ := hadm'
  refine ⟨hM, hconn, hatoms, hbonds, hS.structural, ?_, ?_, hS.hingeOutsideFirst, ?_,
    hS.tripleDesignated, hS.hingeNoLoop⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro v hv
    have hl : atomGapKind G L γ η base (bondIndex G z.1) v = (CoverIndex.choice j).atomLabel v :=
      hlab v
    rw [← hl]
    obtain ⟨x, y, _, _, hxy⟩ := hsub.hingeSG v hv
    exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
  · exact hingeOutsideSecond_of_secondCollectionOK _ L γ η base _ hsec

end WaveTurbulence.GammaLow.FinalCount.H
