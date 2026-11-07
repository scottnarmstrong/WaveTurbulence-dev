/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33ReinsertGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertMateLabels
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.AppBS33SeparatedInvariants
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertNoLoops
import Mathlib.Tactic

/-! # Actual source 3S3-3G output before its optional triple-bond cleanup

The gap loses exactly one L^(-γ). A newly created triple bond is handled
by the subsequent cleanup, so no absence of triple bonds is asserted here.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure S33ReinsertReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  step : GeometricStep (ofMolecule M) (ofMolecule (r.directedPostWithBond 3 5 ⟨1,by decide⟩))
  molecule : (r.directedPostWithBond 3 5 ⟨1,by decide⟩).IsMolecule
  noLoops : AppbNoLoops (r.directedPostWithBond 3 5 ⟨1,by decide⟩)
  largeGap : ∀ ζ,appbS33SeparatedPostAdmissibility r A ζ →
    AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ (g-L^(-γ))
  mateLabels : ∀ ζ,appbS33SeparatedPostAdmissibility r A ζ →
    ∀ x,ζ ((r.directedPostWithBond 3 5 ⟨1,by decide⟩).mate x) = ζ x
  scales : ∀ c,AppbValidLinkScales M L w A c P →
    AppbValidLinkScales (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w
      (appbS33SeparatedPostAdmissibility r A) c
      (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 5) P)
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1 w
      (appbS33SeparatedPostAdmissibility r A)
      (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 5) P))
    (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))

/-- DH23 3S3-3G, actual separated post predicate, graph, physical scales,
and explicit gap loss, under the source defective-pair condition. -/
theorem exists_s33_reinsert_reduction (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.s33.pattern),
    (M.atoms.card : ℝ) ≤ (1+Real.log L)^m → M.IsMolecule → AppbNoLoops M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → AppbS33SplitGeometry M r →
    ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4) →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ g) →
    (∀ κ,A κ → AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      Nonempty (S33ReinsertReduction M r L γ δ C1 g w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_s33_reinsert_good_bound d hd γ hγ m δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hsize hM hno hconn hg hd g w A P hP hLG ht
  have hLp : 0 ≤ L := zero_le_one.trans ((le_max_right L₀ 1).trans hL)
  exact ⟨{
    step := .reinsertS33 (ofMolecule M) r
    molecule := appb_s33_reinsert_isMolecule M hM r hg hd
    noLoops := r.directedPostWithBond_noLoops 3 5 ⟨1,by decide⟩ hno (by decide) (by decide) (by decide)
    largeGap := fun ζ hζ => appb_s33_separated_largeGap r hg hLp w A hLG ht hζ
    mateLabels := fun ζ hζ => s33Separated_mate_labels r hg A hζ
    scales := fun c hc => appb_s33_separated_validLinkScales r hg hc
    deviation := hbase V D C1 hC1 L ((le_max_left L₀ 1).trans hL) M r hsize hM hconn hg w A P hP ht }⟩

end WaveTurbulence.Mole.AppbAlgorithm
