/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceFrequencyRows

/-! # Exact transpose change of the actual leaf phases -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The actual leaf phase is exactly the transpose integer-row phase.
There is no sign change or rescaling in this spatial Fourier identity. -/
theorem sum_inner_inputMomentum_eq_pullback {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Mom d) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    (∑ a, inner ℝ (α a) ((coupleMomentumData hQ hG).inputMomentum k x a)) =
      ∑ c : LinkCoord Q, inner ℝ (sourceFrequencyPullback hQ hG α c) (rootLinkMomenta k x c) := by
  classical
  change (∑ a, inner ℝ (α a) (∑ c : LinkCoord Q,
    sourceNodeRow hQ (plusLeafEquiv hQ hG a).val.toNode c • rootLinkMomenta k x c)) = _
  simp only [sourceFrequencyPullback,inner_sum,sum_inner,← Int.cast_smul_eq_zsmul ℝ,
    real_inner_smul_left,inner_smul_right]
  exact Finset.sum_comm

/-- Separate the root and the two actual link frequencies explicitly. -/
theorem sum_inner_inputMomentum_eq_root_links {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Mom d) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    (∑ a, inner ℝ (α a) ((coupleMomentumData hQ hG).inputMomentum k x a)) =
      inner ℝ (∑ a, α a) k + ∑ j,
        (inner ℝ (sourceFrequencyPullback hQ hG α (some (j,0))) (x j 0) +
          inner ℝ (sourceFrequencyPullback hQ hG α (some (j,1))) (x j 1)) := by
  rw [sum_inner_inputMomentum_eq_pullback hQ hG α k x]
  simp only [Fintype.sum_option,Fintype.sum_prod_type,Fin.sum_univ_two,
    rootLinkMomenta,sourceFrequencyPullback_root]

end WaveTurbulence.RegAsymp
