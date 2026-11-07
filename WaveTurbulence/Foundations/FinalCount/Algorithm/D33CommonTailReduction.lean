/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33NormalReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33PrimaryGoodReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ContinuationInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33PostConnected
import Mathlib.Tactic

/-! # Actual two-step 3D3-1N then 3D3-5G reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

structure D33CommonTailReduction {V : Type v} {D : Type u}
    [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33same.pattern)
    {d : ℕ} (L γ δ η C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  headLabels : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ)
  tailLabels : Fin AppbPatternKind.d33same.pattern.edges.length → (Fin d → ℤ)
  headStep : NormalGeometryStep (ofMolecule M) (ofMolecule r.post) 0
  tailStep : GeometricStep (ofMolecule r.post) (ofMolecule t.post)
  headInvariants : DeletionPostInvariants r L (L^(-γ+η)/2) w A P headLabels
  tailInvariants : DeletionPostInvariants t L (L^(-γ+η)/2) w
    (r.conditionedPostAdmissibility A headLabels) P tailLabels
  deviation : IsDeviation (appbLinkCountA M L γ δ C1 w A P)
    (appbLinkCountA t.post L γ δ C1 w
      (t.conditionedPostAdmissibility (r.conditionedPostAdmissibility A headLabels) tailLabels) P)
    (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))

/-- DH23 algorithm three(c-i), common residual neighbor: the actual normal
head and good tail are composed on the literal successive-deletion carrier.
Every post predicate retains its previous constraints. -/
theorem exists_d33_common_tail_reduction (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    AppbD33BoundaryOpposite M r →
    ∀ t : AppbRealization r.post AppbPatternKind.d33same.pattern,
    ((t.vertex 1 = r.vertex 3 ∧ t.vertex 2 = r.vertex 4) ∨
      (t.vertex 1 = r.vertex 4 ∧ t.vertex 2 = r.vertex 3)) →
    ∀ (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    AppbValidLinkScales M L w A c P → (∀ S,0 ≤ P S) →
    (∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) →
    (∀ κ,A κ → AppbLargeGap M L w κ (L^(-γ+η)/2)) →
      Nonempty (D33CommonTailReduction M r t L γ δ η C1 w A P) := by
  obtain ⟨C₀,hC₀,hn⟩ := exists_d33_normal_reduction d hd γ hγ c hc
  refine ⟨C₀,hC₀,?_⟩
  intro δ hδ
  obtain ⟨Ln,hLn⟩ := hn δ hδ
  obtain ⟨Lg,hLg⟩ := exists_d33_common_good_reduction d hd γ η hγ hη hηγ δ hδ
  refine ⟨max Ln Lg,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hno hnt hconn hb ho t ht w A P hv hP hm hLG
  have hcommon : HasD33ResidualCommon r := ⟨t,ht⟩
  have hdeg := hcommon.boundary_four
  obtain ⟨n⟩ := hLn V D C1 hC1 L ((le_max_left Ln Lg).trans hL) M r hM hno hnt hb ho
    (d33_boundary_four_table r hdeg.1 hdeg.2) (L^(-γ+η)/2) w A P hv hm hLG
  obtain ⟨g⟩ := hLg V _ C1 (hC₀.trans hC1) L ((le_max_right Ln Lg).trans hL) r.post t
    n.invariants.molecule n.invariants.noLoops n.invariants.noTripleBonds
    (d33_post_connected M r hconn hb) (d33_no_new_bridge M r hb hcommon.double_boundary)
    w (r.conditionedPostAdmissibility A n.labels) P hP n.invariants.largeGap
  refine ⟨{
    headLabels := n.labels
    tailLabels := g.labels
    headStep := n.step
    tailStep := g.step
    headInvariants := n.invariants
    tailInvariants := g.invariants
    deviation := ?_ }⟩
  have hn' : appbLinkCountA M L γ δ C1 w A P ≤
      appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A n.labels) P := by
    simpa only [IsDeviation,one_mul] using n.deviation
  exact hn'.trans g.deviation

end WaveTurbulence.Mole.AppbAlgorithm
