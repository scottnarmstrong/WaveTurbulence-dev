/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafCoordinateData
public import WaveTurbulence.Foundations.Incoh.MomentumTreeData

/-! # Actual integer node rows for regular-couple localization -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links

/-- The actual decoration realizing one integer coordinate vector. -/
def coordinateDecoration {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (c : LinkCoord Q) : DecR G ℤ (Incoh.momentumUnitRow c none) :=
  decOfParams hQ (Incoh.momentumUnitRow c none)
    (fun j => (Incoh.momentumUnitRow c (some (j,0)), Incoh.momentumUnitRow c (some (j,1))))

/-- Each selected row is read from an actual source decoration. -/
def sourceNodeRow {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (a : GNode G.tree) : LinkCoord Q → ℤ := fun c => (coordinateDecoration hQ c).val a

/-- Coordinates of the basis decorations are exactly the integer basis. -/
theorem linkCoords_coordinateDecoration {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (c : LinkCoord Q) :
    linkCoords Q (coordinateDecoration hQ c).val = Incoh.momentumUnitRow c := by
  funext z
  cases z with
  | none => exact (coordinateDecoration hQ c).property.2 0
  | some z =>
    obtain ⟨j,i⟩ := z
    have hp := congrFun (decParams_decOfParams hQ hG (Incoh.momentumUnitRow c none)
      (fun j => (Incoh.momentumUnitRow c (some (j,0)), Incoh.momentumUnitRow c (some (j,1))))) j
    rcases fin_two_cases i with rfl | rfl
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp

/-- The root column is one at every actual node, not just the inputs. -/
theorem sourceNodeRow_root_column {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (a : GNode G.tree) : sourceNodeRow hQ a none = 1 := by
  obtain ⟨A,B,h⟩ := node_linear hQ a
  have hh := h ℤ (Incoh.momentumUnitRow (n := Q.links.length) none none)
    (fun j => (Incoh.momentumUnitRow none (some (j,0)), Incoh.momentumUnitRow none (some (j,1))))
  simpa [sourceNodeRow,coordinateDecoration,Incoh.momentumUnitRow] using hh

/-- Every root row selects precisely the root coordinate. -/
theorem sourceNodeRow_root {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (i : Fin 2) :
    sourceNodeRow hQ (GNode.root G.tree i) = Incoh.momentumUnitRow none := by
  funext c
  have hh := (coordinateDecoration hQ c).property.2 i
  simpa only [sourceNodeRow,Incoh.momentumUnitRow,eq_comm] using hh

/-- Paired leaves have identical rows. -/
theorem sourceNodeRow_pair {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (ℓ : GLeaf G.tree) :
    sourceNodeRow hQ ℓ.toNode = sourceNodeRow hQ (G.pair ℓ).toNode := by
  funext c
  exact (coordinateDecoration hQ c).property.1.2 ℓ

end WaveTurbulence.RegAsymp
