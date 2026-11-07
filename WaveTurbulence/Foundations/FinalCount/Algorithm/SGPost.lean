/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGProblem
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGDeletionValue
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestBranches
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestInitialData
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActiveEditBounds
public import WaveTurbulence.Foundations.FinalCount.AppBEncodedRemovalProperties
import Mathlib.Tactic

/-! # The post problem after removing the exceptional atoms

Removing the exceptional set `S` of an SG problem along an actual realization leaves a genuine
large-gap `Problem` (not necessarily connected), together with the graph bookkeeping needed to
feed the forest core (DH23 L1834, `w` SG atoms).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Finset
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}

/-- The conditioned post problem of an SG problem along a realization of the removal of the
exceptional set; its admissible decorations are large gap everywhere. -/
noncomputable def ProblemSG.post {ws : ℕ} (p : ProblemSG.{u,v} V d L w c g ws) {P : AppbPattern}
    (r : AppbRealization p.state.graph P) (q : Fin P.edges.length → (Fin d → ℤ)) :
    Problem.{u,v} V d L w c g where
  state := ofMolecule r.post
  admissible := r.conditionedPostAdmissibility
    (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph r.removedAtoms L w κ g) q
  scales := p.scales
  molecule := appb_eraseAtoms_isMolecule p.state.graph p.molecule r.removedAtoms
  noLoops := appb_eraseAtoms_noLoops p.state.graph r.removedAtoms p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := r.conditionedPost_validLinkScales
    (p.validLinkScales.mono (fun κ hκ => hκ.1)) q
  mateLabels := conditionedPost_mate_labels r _ q
  largeGap := by
    rintro ζ ⟨κ,⟨hκ,hg⟩,hm,hq,hr⟩
    rw [← hr]
    exact appb_largeGapOff_eraseAtoms p.state.graph r.removedAtoms hg

theorem ProblemSG.post_value {ws : ℕ} (p : ProblemSG.{u,v} V d L w c g ws) {P : AppbPattern}
    (r : AppbRealization p.state.graph P) (q : Fin P.edges.length → (Fin d → ℤ)) (γ δ C1 : ℝ) :
    (p.post r q).value γ δ C1 = appbLinkCountA r.post L γ δ C1 w
      (r.conditionedPostAdmissibility
        (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph r.removedAtoms L w κ g) q)
      p.scales := rfl

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem balancedPotential_ge_nonFour_disconnected (M : Molecule V D) (hM : M.IsMolecule) (w : ℕ)
    (hw : (M.atoms.filter (fun a => M.deg a ≠ 4)).card ≤ w) :
    -(396 : ℤ)*w ≤ balancedPotential M := by
  have hd := degreeDeficit_le_nonFour M w hw
  have hh := degree_sum_add_deficit M hM
  have hs := special_count_le_two_degreeThree M hM
  have hF : (0 : ℤ) ≤ M.numComponents := by positivity
  have hnu : appbNu M ≤ (degreeDeficit M : ℤ) := by
    unfold appbNu
    have : (2*M.bonds.card+degreeDeficit M : ℤ) = 4*M.atoms.card := by exact_mod_cast hh
    linarith only [this,hF]
  have h3 : (0 : ℤ) ≤ (appbDegreeAtoms M 3).card := by positivity
  have h2 : (0 : ℤ) ≤ (simpleDegreeTwoAtoms M).card := by positivity
  have hsz : ((appbSpecialBonds M).card : ℤ) ≤ 2*(appbDegreeAtoms M 3).card := by exact_mod_cast hs
  have hdz : (degreeDeficit M : ℤ) ≤ 4*w := by exact_mod_cast hd
  unfold balancedPotential
  omega

theorem AppbPattern.card_vertices_le (P : AppbPattern) :
    P.vertices.card ≤ P.removed.card+2*P.edges.length := by
  unfold AppbPattern.vertices
  refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_flatMap]
  simp [mul_comm]

end WaveTurbulence.Mole.AppbAlgorithm
