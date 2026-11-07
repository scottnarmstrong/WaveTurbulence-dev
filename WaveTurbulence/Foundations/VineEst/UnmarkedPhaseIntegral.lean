/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.GraftTimeSplit
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Phase integrals of plain gardens are ordinary integrals over all branching times. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory

theorem not_flowerParent_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, _⟩
  have hm := hG ℓ
  have he := hm.symm.trans hℓ
  cases he

noncomputable def freeBranchEquivOfNoFlowerParent {w : ℕ} (G : Garden w)
    (hG : ∀ b, ¬ G.IsFlowerParent b) : G.FreeBranch ≃ GBranch G.tree :=
  Equiv.subtypeUnivEquiv hG

theorem phaseIntegral_of_no_flowerParent {d w : ℕ} (L γ δ : ℝ) (G : Garden w)
    (hG : ∀ b, ¬ G.IsFlowerParent b)
    (D : Set (GBranch G.tree → ℝ)) (s : ℝ) (k : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s k = ∫ τ, D.indicator (phaseProd L γ δ G k) τ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ => ℝ) (freeBranchEquivOfNoFlowerParent G hG)
  have ht (τ : G.FreeBranch → ℝ) : G.extendTime s τ = e τ := by
    funext b
    simp only [Garden.extendTime, hG b, dite_false]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : GBranch G.tree => (volume : Measure ℝ))
    (freeBranchEquivOfNoFlowerParent G hG)
  exact (integral_congr_ae (ae_of_all _ (fun τ =>
    congrArg (D.indicator (phaseProd L γ δ G k)) (ht τ)))).trans
      (hmp.integral_comp' (D.indicator (phaseProd L γ δ G k)))

theorem phaseIntegral_of_plain {d w : ℕ} (L γ δ : ℝ) (G : Garden w) (hG : G.IsPlain)
    (D : Set (GBranch G.tree → ℝ)) (s : ℝ) (k : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s k = ∫ τ, D.indicator (phaseProd L γ δ G k) τ :=
  phaseIntegral_of_no_flowerParent L γ δ G (not_flowerParent_of_plain G hG) D s k

end WaveTurbulence.LGSpine
