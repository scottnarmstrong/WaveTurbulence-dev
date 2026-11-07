/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.FineGeometryStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFineHalfGap
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ConditionedDeletionInvariants
import Mathlib.Tactic

/-! # An actual selected fine reduction with its inherited analytic problem

The source theorem constructs all fields from the chosen literal figure
and proved counting estimates. No deviation or post-invariant conclusion
is an assumption of the selector-completeness theorem.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v
variable {V : Type v} [DecidableEq V]

structure FineReduction (s : State.{u,v} V) {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d)
    (A : (s.Dart → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  target : State.{u,v} V
  admissible : (target.Dart → (Fin d → ℤ)) → Prop
  step : FineGeometryStep s target
  molecule : target.graph.IsMolecule
  noLoops : AppbNoLoops target.graph
  noTripleBonds : AppbNoTripleBonds target.graph
  largeGap : ∀ ζ,admissible ζ → AppbLargeGap target.graph L w ζ (L^(-γ+η)/2)
  largeGapInherited : ∀ g,(∀ κ,A κ → AppbLargeGap s.graph L w κ g) →
    ∀ ζ,admissible ζ → AppbLargeGap target.graph L w ζ g
  mateLabels : ∀ ζ,admissible ζ → ∀ x,ζ (target.graph.mate x) = ζ x
  validLinkScales : ∀ c,AppbValidLinkScales s.graph L w A c P →
    AppbValidLinkScales target.graph L w admissible c P
  deviation : IsDeviation (appbLinkCountA s.graph L γ δ C1 w A P)
    (appbLinkCountA target.graph L γ δ C1 w admissible P) (ENNReal.ofReal (L^(-η/2)))

/-- Internal conditional packaging of a literal deletion. The source
selector below supplies the deviation from a proved operation estimate. -/
private noncomputable def fineReductionOfDeletion {D : Type u} [Fintype D] [DecidableEq D]
    (M : Molecule V D) {B : AppbPattern} (r : AppbRealization M B)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (q : Fin B.edges.length → (Fin d → ℤ))
    (hM : M.IsMolecule) (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (hLG : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2))
    (hs : FineGeometryStep (ofMolecule M) (ofMolecule r.post))
    (hd : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
      (appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A q) P)
      (ENNReal.ofReal (L^(-η/2)))) : FineReduction (ofMolecule M) L γ δ η C1 w A P where
  target := ofMolecule r.post
  admissible := r.conditionedPostAdmissibility A q
  step := hs
  molecule := appb_eraseAtoms_isMolecule M hM r.removedAtoms
  noLoops := appb_eraseAtoms_noLoops M r.removedAtoms hno
  noTripleBonds := appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt
  largeGap := conditionedPost_largeGap r q hLG
  largeGapInherited := fun g hg => conditionedPost_largeGap r q hg
  mateLabels := conditionedPost_mate_labels r A q
  validLinkScales := fun c hv => r.conditionedPost_validLinkScales hv q
  deviation := hd

/-- DH23 Appendix B rule seven: the actual fine figure always produces
a complete next counting problem, with carrier-uniform threshold and the
iterated half-gap premise. Earlier tests exclude bridges and degree three. -/
theorem exists_rule_seven_fine_reduction (d : ℕ) (hd : 2 ≤ d) (δ γ η C1 : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hC1 : 1 ≤ C1) :
    ∃ L₀ : ℝ,∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ L ≥ L₀,∀ (M : Molecule V D),M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    (∀ e : D,¬Degen.IsBridge M e) → (∀ a ∈ M.atoms,M.deg a ≠ 3) → M.bonds.Nonempty →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (FineReduction (ofMolecule M) L γ δ η C1 w A P) := by
  obtain ⟨Lt,ht⟩ := uniform_r2_two_bond_half_gap_fine_bound d hd δ γ η C1 hδ hγ hη hηγ hC1
  obtain ⟨Lo,ho⟩ := uniform_r23_open_half_gap_fine_bound d hd δ γ η C1 hδ hγ hη hηγ hC1
  obtain ⟨Lr,hr⟩ := uniform_r23_triangle_half_gap_fine_bound d hd δ γ η C1 hδ hγ hη hηγ hC1
  obtain ⟨Lc,hc⟩ := uniform_r23_common_half_gap_fine_bound d hd δ γ η C1 hδ hγ hη hηγ hC1
  refine ⟨max (max Lt Lo) (max Lr Lc),?_⟩
  intro V D instV instF instD L hL M hM hno hnt hconn hb h3 hne w A P hLG
  have hLt := (le_max_left Lt Lo).trans ((le_max_left (max Lt Lo) _).trans hL)
  have hLo := (le_max_right Lt Lo).trans ((le_max_left (max Lt Lo) _).trans hL)
  have hLr := (le_max_left Lr Lc).trans ((le_max_right _ (max Lr Lc)).trans hL)
  have hLc := (le_max_right Lr Lc).trans ((le_max_right _ (max Lr Lc)).trans hL)
  have sel := exists_degree_two_selection M hM hno hb h3 hne
  cases sel with
  | doubleFour r h =>
    obtain ⟨q,hq⟩ := ht V D L hLt M .r21 (by decide) r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.table (ofMolecule M) .r21 (by decide) r h hb) hq⟩
  | singleFour r h hd3 =>
    obtain ⟨q,hq⟩ := ht V D L hLt M .r22 (by decide) r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.table (ofMolecule M) .r22 (by decide) r ⟨h,hd3⟩ hb) hq⟩
  | triangle r =>
    obtain ⟨q,hq⟩ := hr V D L hLr M r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.table (ofMolecule M) .r23triangle (by decide) r trivial hb) hq⟩
  | common r =>
    obtain ⟨q,hq⟩ := hc V D L hLc M r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.common (ofMolecule M) r (h3 _ (r.vertex_mem 4 (by decide))) hb) hq⟩
  | chain r =>
    obtain ⟨q,hq⟩ := ho V D L hLo M r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.table (ofMolecule M) .r23 (by decide) r
        ⟨h3 _ (r.vertex_mem 4 (by decide)),h3 _ (r.vertex_mem 5 (by decide))⟩ hb) hq⟩
  | doubleTwo r =>
    obtain ⟨q,hq⟩ := ht V D L hLt M .r24 (by decide) r hconn hb w A hLG P
    exact ⟨fineReductionOfDeletion M r L γ δ η C1 w A P q hM hno hnt hLG
      (.table (ofMolecule M) .r24 (by decide) r trivial hb) hq⟩

end WaveTurbulence.Mole.AppbAlgorithm
