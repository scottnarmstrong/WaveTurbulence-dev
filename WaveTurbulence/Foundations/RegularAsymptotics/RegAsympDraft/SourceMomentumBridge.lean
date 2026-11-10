/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleCellCover
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeRowEvaluation

/-! # Localization input momenta are the actual source leaf momenta -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh

/-- The structural input momentum is precisely the leaf of the actual
source decoration, for every additive carrier and every free coordinate. -/
theorem coupleMomentumData_inputMomentum {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {V : Type} [AddCommGroup V]
    (r : V) (x : Fin Q.links.length → Fin 2 → V) (a : Fin (2*Q.links.length+1)) :
    (coupleMomentumData hQ hG).inputMomentum r x a =
      (decOfParams hQ r (fun j => (x j 0,x j 1))).val (plusLeafEquiv hQ hG a).val.toNode := by
  have hx : rootLinkMomenta r x = fun c : LinkCoord Q => match c with
    | none => r | some (j,i) => if i=0 then x j 0 else x j 1 := by
    funext c
    cases c with
    | none => rfl
    | some c =>
      obtain ⟨j,i⟩ := c
      rcases fin_two_cases i with rfl | rfl <;> simp [rootLinkMomenta]
  change momentumRowEval (rootLinkMomenta r x) (sourceNodeRow hQ _) = _
  rw [hx]
  exact sourceNodeRow_eval hQ _ r (fun j => (x j 0,x j 1))

end WaveTurbulence.RegAsymp
