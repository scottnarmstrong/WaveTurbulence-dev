/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTopPhase
public import WaveTurbulence.Foundations.XChain.GraftPlainPhaseIntegral
/-! In the plain case every top branching time is free and the top phase is the forest phase. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem graftTopPhaseIntegral_of_plain {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hplain : ∀ B, (low B).IsPlain) (k : GNode top → Mom d) (p t s : ℝ) :
    graftTopPhaseIntegral L γ δ sig top P low hsig k p t s = forestPhaseIntegral L γ δ sig top k p t := by
  classical
  have hn : ∀ b : GBranch top, ¬ (markedGardenGraft sig top P low hsig).IsFlowerParent
      (gardenBranchEquiv top P low (.inl b)) :=
    fun b => not_flowerParent_of_plain _ (markedGardenGraft_isPlain sig top P low hsig hplain) _
  let e := MeasurableEquiv.piCongrLeft (fun _ : GBranch top => ℝ) (Equiv.subtypeUnivEquiv hn)
  have he (τ : GraftTopFreeBranch sig top P low hsig → ℝ) :
      graftTopExtendTime sig top P low hsig s τ = e τ := by
    funext b
    simp only [graftTopExtendTime, hn b ]
    rfl
  have hm := measurePreserving_piCongrLeft (fun _ : GBranch top => (volume : Measure ℝ))
    (Equiv.subtypeUnivEquiv hn)
  have hi := integral_congr_ae (μ := (volume : Measure (GraftTopFreeBranch sig top P low hsig → ℝ)))
    (ae_of_all _ (fun τ => congrArg
      ((ForestTimeDomain top p t).indicator (forestPhaseProd L γ δ sig top k)) (he τ)))
  exact hi.trans (hm.integral_comp' ((ForestTimeDomain top p t).indicator (forestPhaseProd L γ δ sig top k)))

end WaveTurbulence.Induct
