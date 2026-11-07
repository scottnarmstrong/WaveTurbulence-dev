/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33ReinsertGood
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertMateLabels
public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertNoLoops
import Mathlib.Tactic

/-! # Actual source 3D3-3G output before its optional triple-bond cleanup

The gap loses exactly one L^(-γ). A newly created triple bond is handled
by the subsequent cleanup, so no absence of triple bonds is asserted here.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure D33ReinsertReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern)
    {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  step : GeometricStep (ofMolecule M) (ofMolecule (r.directedPostWithBond 3 4 ⟨2,by decide⟩))
  molecule : (r.directedPostWithBond 3 4 ⟨2,by decide⟩).IsMolecule
  noLoops : AppbNoLoops (r.directedPostWithBond 3 4 ⟨2,by decide⟩)
  largeGap : ∀ ζ,r.reinsertedPostAdmissibility A ⟨2,by decide⟩ ζ →
    AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w ζ (g-L^(-γ))
  mateLabels : ∀ ζ,r.reinsertedPostAdmissibility A ⟨2,by decide⟩ ζ →
    ∀ x,ζ ((r.directedPostWithBond 3 4 ⟨2,by decide⟩).mate x) = ζ x
  scales : ∀ c,AppbValidLinkScales M L w A c P →
    AppbValidLinkScales (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w
      (r.reinsertedPostAdmissibility A ⟨2,by decide⟩) c
      (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 4) P)
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1 w
      (r.reinsertedPostAdmissibility A ⟨2,by decide⟩)
      (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 4) P))
    (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))

/-- DH23 3D3-3G, actual inherited post predicate, graph, physical scales,
and explicit gap loss, under the source nonsaturated-component condition. -/
theorem exists_d33_reinsert_reduction (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ (1 : ℝ),∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → AppbD33BoundaryOpposite M r →
    (∀ e : D,¬Degen.IsBridge M e) → AppbD33ResidualDefect M r →
    ∀ (g : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ S,0 ≤ P S) → (∀ κ,A κ → AppbLargeGap M L w κ g) →
    (∀ κ,A κ → AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      Nonempty (D33ReinsertReduction M r L γ δ C1 g w A P) := by
  intro δ hδ
  obtain ⟨L₀,hbase⟩ := uniform_d33_reinsert_good_bound d hd γ hγ δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hconn hg hb hd g w A P hP hLG ht
  have hLp : 0 ≤ L := zero_le_one.trans ((le_max_right L₀ 1).trans hL)
  exact ⟨{
    step := .reinsertD33 (ofMolecule M) r
    molecule := appb_d33_reinsert_isMolecule M hM r hconn hb hg hd
    noLoops := r.directedPostWithBond_noLoops 3 4 ⟨2,by decide⟩ hno (by decide) (by decide) (by decide)
    largeGap := by
      intro ζ hζ
      obtain ⟨κ,hκ,hm,rfl⟩ := hζ
      exact appb_d33_reinsert_largeGap r hg w κ hm (hLG κ hκ) (ht κ hκ) hLp
    mateLabels := fun ζ hζ => reinsertedPost_mate_labels r A 3 4 ⟨2,by decide⟩ hζ
    scales := fun c hc => r.reinsertedPost_validLinkScales 3 4 ⟨2,by decide⟩ hc
    deviation := hbase V D C1 hC1 L ((le_max_left L₀ 1).trans hL) M r hM hconn hb hg w A P hP ht }⟩

end WaveTurbulence.Mole.AppbAlgorithm
