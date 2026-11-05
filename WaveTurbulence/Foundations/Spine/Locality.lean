/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderL1Gate
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSplit
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
public import WaveTurbulence.Foundations.Spine.SplicedTimeIntegrability
public import WaveTurbulence.Foundations.Spine.FiniteCosetBall
/-! # Locality and factorisation of the spliced integrand over disjoint ladders (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w}

/-- Slot-node labels at an atom are determined by the bond labels at its darts. -/
lemma slot_eq_of_atom (hP : G.IsPlain) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0) (a : GBranch G.tree)
    (h : ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z'.1 x) :
    z.1 a.toNode = z'.1 a.toNode ∧ z.1 (a.child 0) = z'.1 (a.child 0) ∧
      z.1 (a.child 1) = z'.1 (a.child 1) ∧ z.1 (a.child 2) = z'.1 (a.child 2) :=
  ⟨node_label_local hP roots z z' a h 0, node_label_local hP roots z z' a h 1,
    node_label_local hP roots z z' a h 2, node_label_local hP roots z z' a h 3⟩

/-- The ladder weight only depends on the bond labels at darts of the ladder atoms. -/
lemma ladderWeight_congr (hP : G.IsPlain) (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0)
    (h : ∀ x, G.molecule.atom x ∈ S → bondIndex G z.1 x = bondIndex G z'.1 x) :
    ladderWeight D S L γ η base z.1 = ladderWeight D S L γ η base z'.1 := by
  unfold ladderWeight
  have heps : ∀ v ∈ S, epsCoef (z.1 (v.child 0)) (z.1 (v.child 1)) (z.1 (v.child 2)) =
      epsCoef (z'.1 (v.child 0)) (z'.1 (v.child 1)) (z'.1 (v.child 2)) := by
    intro v hv
    obtain ⟨-, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z' v (fun x hx => h x (by rw [hx]; exact hv))
    rw [h0, h1, h2]
  have hgap : localLadderGapIndicator G D S L γ η base z.1 =
      localLadderGapIndicator G D S L γ η base z'.1 := by
    unfold localLadderGapIndicator
    apply prod_congr rfl
    intro v hv
    cases hq : D.gapSpecification v with
    | none => rfl
    | some q =>
      dsimp only
      rw [h q.first (by rw [q.at_first]; exact hv), h q.second (by rw [q.at_second]; exact hv)]
  have hedge : (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) =
      ∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G z'.1 x)) := by
    apply prod_congr rfl
    intro x hx
    rw [h x (mem_filter.mp hx).2.1]
  rw [Finset.prod_congr rfl (fun v hv => congrArg (fun r : ℝ => (r : ℂ)) (heps v hv)), hgap, hedge]

/-- The ladder phase only depends on the bond labels at darts of the ladder atoms. -/
lemma ladderPhase_congr (hP : G.IsPlain) (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0)
    (h : ∀ x, G.molecule.atom x ∈ S → bondIndex G z.1 x = bondIndex G z'.1 x) :
    ladderPhase D S L γ δ base z.1 = ladderPhase D S L γ δ base z'.1 := by
  funext t
  unfold ladderPhase
  apply prod_congr rfl
  intro v _
  obtain ⟨hr, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z' v.1 (fun x hx => h x (by rw [hx]; exact v.2))
  unfold omegaNode resFactor cosetDecoration
  rw [hr, h0, h1, h2]

/-- The ladder phase at the restricted global times is the product of the global exponentials. -/
lemma ladderPhase_eq_prod (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (t : GBranch G.tree → ℝ) :
    ladderPhase D S L γ δ base z (fun v : S => t v.1) =
      ∏ v ∈ S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z v * t v : ℝ) * Complex.I) := by
  unfold ladderPhase
  rw [← Finset.prod_coe_sort S]
  apply prod_congr rfl
  intro v _
  congr 1
  unfold splicedFrequency
  push_cast
  ring

end WaveTurbulence.CoarseSpliced
