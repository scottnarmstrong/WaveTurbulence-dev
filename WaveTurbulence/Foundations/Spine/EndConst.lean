/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightSplit
public import WaveTurbulence.Foundations.Spine.NodeLocal
public import WaveTurbulence.Foundations.Spine.LadderPhase
/-! # End-atom factors depend only on the labels at the end darts (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

lemma atomFac_eq_of_agree (hP : G.IsPlain) (roots : Fin w → (Fin d → ℤ))
    (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (z z' : GenDecoration G d roots 0) (a : GBranch G.tree)
    (h : ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z'.1 x) :
    atomFac D L γ η base z.1 a = atomFac D L γ η base z'.1 a := by
  have hn : ∀ j : Fin 3, z.1 (a.child j) = z'.1 (a.child j) := fun j =>
    node_label_local hP roots z z' a h j.succ
  unfold atomFac
  rw [hn 0, hn 1, hn 2]
  congr 1
  rcases hs : D.gapSpecification a with _ | q
  · rfl
  · simp only [gapAtomSpec]
    rw [h q.first q.at_first, h q.second q.at_second]

lemma phaseAt_eq_of_agree (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (D : SplicedKernelData G d) (γ δ : ℝ)
    (z z' : GenDecoration G d roots 0) (a : GBranch G.tree)
    (h : ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z'.1 x) (τ : ℝ) :
    phaseAt D L γ δ base z.1 a τ = phaseAt D L γ δ base z'.1 a τ := by
  have hz := phase_exponent hP hL base roots z a
  have hz' := phase_exponent hP hL base roots z' a
  have hG : G.molecule.Gamma L base (bondIndex G z.1) a = G.molecule.Gamma L base (bondIndex G z'.1) a := by
    unfold Molecule.Gamma
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxa : G.molecule.atom x = a := (Finset.mem_filter.mp hx).2
    simp only [Molecule.kvec, h x hxa]
  have he : ((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ)) * omegaNode G (cosetDecoration G L base z.1) a =
      ((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ)) * omegaNode G (cosetDecoration G L base z'.1) a := by
    rw [hz, hz', hG]
  unfold phaseAt
  have e1 : ∀ y : GNode G.tree → (Fin d → ℤ), ((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      omegaNode G (cosetDecoration G L base y) a) =
      δ * L ^ (2 * γ) * ((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G (cosetDecoration G L base y) a) :=
    fun y => by ring
  rw [e1, e1, he]

end WaveTurbulence.LadderDecay
