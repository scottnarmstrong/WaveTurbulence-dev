/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
/-! TARGET L2067: simultaneous translation leaves each decorated resonance and phase unchanged. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory
open scoped RealInnerProductSpace

theorem resFactor_add_common {d : ℕ} (a x₁ x₂ x₃ x₄ : Mom d)
    (hsum : x₄ = x₁ - x₂ + x₃) :
    resFactor (a + x₁) (a + x₂) (a + x₃) (a + x₄) = resFactor x₁ x₂ x₃ x₄ := by
  have hi : inner ℝ a x₄ = inner ℝ a x₁ - inner ℝ a x₂ + inner ℝ a x₃ := by
    rw [hsum, inner_add_right, inner_sub_right]
  simp only [resFactor, norm_add_sq_real]
  linarith

theorem latticePoint_decoration_consistent {w d : ℕ} (G : Garden w) (L : ℝ)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (b : GBranch G.tree) :
    latticePoint L (z b.toNode) = latticePoint L (z (b.child 0)) -
      latticePoint L (z (b.child 1)) + latticePoint L (z (b.child 2)) := by
  rw [hz.1 b]
  ext j
  simp only [latticePoint, PiLp.add_apply, PiLp.sub_apply, Pi.add_apply, Pi.sub_apply,
    Int.cast_add, Int.cast_sub, add_div, sub_div]

theorem omegaNode_coset_eq_zero {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (b : GBranch G.tree) :
    omegaNode G (cosetDecoration G L k z) b = omegaNode G (cosetDecoration G L 0 z) b := by
  simp only [omegaNode, cosetDecoration, zero_add]
  exact resFactor_add_common k _ _ _ _ (latticePoint_decoration_consistent G L z hz b)

theorem phaseProd_coset_eq_zero {w d : ℕ} (L γ δ : ℝ) (G : Garden w) (k : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z)
    (τ : GBranch G.tree → ℝ) :
    phaseProd L γ δ G (cosetDecoration G L k z) τ =
      phaseProd L γ δ G (cosetDecoration G L 0 z) τ := by
  unfold phaseProd
  apply Finset.prod_congr rfl
  intro b _
  rw [omegaNode_coset_eq_zero G L k z hz b]

theorem phaseIntegral_coset_eq_zero {w d : ℕ} (L γ δ : ℝ) (G : Garden w)
    (D : Set (GBranch G.tree → ℝ)) (s : ℝ) (k : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) :
    phaseIntegral L γ δ G D s (cosetDecoration G L k z) =
      phaseIntegral L γ δ G D s (cosetDecoration G L 0 z) := by
  have he : phaseProd L γ δ G (cosetDecoration G L k z) =
      phaseProd L γ δ G (cosetDecoration G L 0 z) :=
    funext (phaseProd_coset_eq_zero L γ δ G k z hz)
  simp only [phaseIntegral, he]

end WaveTurbulence.LGSpine
