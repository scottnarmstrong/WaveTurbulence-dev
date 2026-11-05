/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeCoordinateRows

/-! # Integer rows evaluate to the actual source node values -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links

/-- The node rows extracted from basis decorations recover every actual
C2 decoration on an arbitrary additive carrier. -/
theorem sourceNodeRow_eval {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (a : GNode G.tree) {V : Type} [AddCommGroup V] (r : V)
    (θ : Fin Q.links.length → V × V) :
    Incoh.momentumRowEval (fun c => match c with
      | none => r
      | some (j,i) => if i=0 then (θ j).1 else (θ j).2) (sourceNodeRow hQ a) =
      (decOfParams hQ r θ).val a := by
  classical
  obtain ⟨A,B,h⟩ := node_linear hQ a
  have hrow0 (j : Fin Q.links.length) : sourceNodeRow hQ a (some (j,0)) = A j := by
    have hh := h ℤ (Incoh.momentumUnitRow (some (j,0)) none)
      (fun l => (Incoh.momentumUnitRow (some (j,0)) (some (l,0)),
        Incoh.momentumUnitRow (some (j,0)) (some (l,1))))
    simpa [sourceNodeRow,coordinateDecoration,Incoh.momentumUnitRow] using hh
  have hrow1 (j : Fin Q.links.length) : sourceNodeRow hQ a (some (j,1)) = B j := by
    have hh := h ℤ (Incoh.momentumUnitRow (some (j,1)) none)
      (fun l => (Incoh.momentumUnitRow (some (j,1)) (some (l,0)),
        Incoh.momentumUnitRow (some (j,1)) (some (l,1))))
    simpa [sourceNodeRow,coordinateDecoration,Incoh.momentumUnitRow] using hh
  rw [h V r θ]
  change (∑ c : LinkCoord Q, sourceNodeRow hQ a c • (match c with
    | none => r | some (j,i) => if i=0 then (θ j).1 else (θ j).2)) = _
  simp [Fintype.sum_option,Fintype.sum_prod_type,Fin.sum_univ_two,
    sourceNodeRow_root_column hQ a,hrow0,hrow1]

end WaveTurbulence.RegAsymp
