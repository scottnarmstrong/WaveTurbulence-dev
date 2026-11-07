/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32RankFourGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32RankFiveGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CombinedPostInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CombinedPostEquality
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.AppBHalfGap
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # The complete good branch of source rule six on the literal post graph -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Filter
universe u v

structure R32GoodReduction {V : Type v} {D : Type u} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
    (t : AppbRealization r.post AppbPatternKind.s33new3.pattern)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  admissible : (Degen.RetainedDart r.post t.removedAtoms → (Fin d → ℤ)) → Prop
  step : GeometricStep (ofMolecule M) (ofMolecule t.post)
  molecule : t.post.IsMolecule
  noLoops : AppbNoLoops t.post
  noTripleBonds : AppbNoTripleBonds t.post
  largeGap : ∀ ζ,admissible ζ → AppbLargeGap t.post L w ζ (L^(-γ+η)/2)
  largeGapInherited : ∀ g,(∀ κ,A κ → AppbLargeGap M L w κ g) →
    ∀ ζ,admissible ζ → AppbLargeGap t.post L w ζ g
  mateLabels : ∀ ζ,admissible ζ → ∀ x,ζ (t.post.mate x) = ζ x
  validLinkScales : ∀ c,AppbValidLinkScales M L w A c P → AppbValidLinkScales t.post L w admissible c P
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA t.post L γ δ C1 w admissible P) (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))

/-- DH23 3R-2G: both actual component outcomes, the concrete post
predicate, and every inherited physical input. The size/half-gap premises
are precisely the standing iterated-algorithm ones. -/
theorem exists_r32_good_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ,∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.r3.pattern)
      (t : AppbRealization r.post AppbPatternKind.s33new3.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) →
    (∀ e : D,¬Degen.IsBridge M e) → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (R32GoodReduction M r t L γ δ η C1 w A P) := by
  have hη' : 0 < 2*η/3 := by linarith only [hη]
  have hηγ' : 2*η/3 ≤ min γ (1-γ) := by linarith only [hη,hηγ]
  obtain ⟨L4,h4⟩ := uniform_r32_rank_four_good_bound d hd γ hγ δ (2*η/3) hδ hη' hηγ' m
  obtain ⟨L5,h5⟩ := uniform_r32_rank_five_good_bound d hd γ hγ δ hδ
  obtain ⟨Lh,hh⟩ := eventually_atTop.mp (appb_half_gap_comparison_eventual γ η hη)
  refine ⟨max L4 (max L5 Lh),?_⟩
  intro V D instV instF instD C1 hC1 L hL M r t hM hno hnt hconn hb hsize w A P hP hLG
  have hL4 := (le_max_left L4 _).trans hL
  have hL5 := (le_max_left L5 Lh).trans ((le_max_right L4 _).trans hL)
  have hLh := (le_max_right L5 Lh).trans ((le_max_right L4 _).trans hL)
  have hM1 := appb_eraseAtoms_isMolecule M hM r.removedAtoms
  have hM2 := appb_eraseAtoms_isMolecule r.post hM1 t.removedAtoms
  have hno1 := appb_eraseAtoms_noLoops M r.removedAtoms hno
  have hno2 := appb_eraseAtoms_noLoops r.post t.removedAtoms hno1
  have hnt1 := appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt
  have hnt2 := appb_eraseAtoms_noTripleBonds r.post t.removedAtoms hnt1
  rcases appb_r32_graph_effect M r t hconn hb with hF | hF
  · obtain ⟨q1,q2,hq⟩ := h5 V D C1 hC1 L hL5 M r t hM hF.1 w A P hP
    exact ⟨{
      admissible := t.conditionedPostAdmissibility (r.conditionedPostAdmissibility A q1) q2
      step := .r32 (ofMolecule M) r t
      molecule := hM2
      noLoops := hno2
      noTripleBonds := hnt2
      largeGap := conditionedPost_largeGap t q2 (conditionedPost_largeGap r q1 hLG)
      largeGapInherited := fun g hg => conditionedPost_largeGap t q2 (conditionedPost_largeGap r q1 hg)
      mateLabels := conditionedPost_mate_labels t _ q2
      validLinkScales := fun _ hv => t.conditionedPost_validLinkScales (r.conditionedPost_validLinkScales hv q1) q2
      deviation := hq }⟩
  · have hMF := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
    have hF2 : t.post.numComponents = 2 := by omega
    have hLG' : ∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+2*η/3)) :=
      fun κ hκ => (hLG κ hκ).mono (hh L hLh)
    let v0 : M.atoms := ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩
    obtain ⟨q,hq⟩ := h4 V D C1 hC1 L hL4 M r t v0 hM hconn hb hF2 hsize w A P hP hLG'
    change appbLinkCountA M L γ δ C1 w A P ≤
      ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*
        appbLinkCountA (r.combinedRemoval t v0).post L γ δ C1 w
          ((r.combinedRemoval t v0).conditionedPostAdmissibility A q) P at hq
    rw [combinedPost_countA_eq_sequential r t v0 L γ δ C1 w A q P] at hq
    exact ⟨{
      admissible := combinedSequentialAdmissibility r t v0 A q
      step := .r32 (ofMolecule M) r t
      molecule := hM2
      noLoops := hno2
      noTripleBonds := hnt2
      largeGap := combinedSequential_largeGap r t v0 q hLG
      largeGapInherited := fun g hg => combinedSequential_largeGap r t v0 q hg
      mateLabels := combinedSequential_mate_labels r t v0 A q
      validLinkScales := fun _ hv => combinedSequential_validLinkScales r t v0 q hv
      deviation := hq }⟩

end WaveTurbulence.Mole.AppbAlgorithm
