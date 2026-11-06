/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderCtx
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
/-! # Labels of the darts at a garden atom by position (S3b LADDER-DECAY)

The four darts at an atom of degree four sit at the positions `0` (parent) and `1,2,3` (the
children); the label of the dart at position `j+1` is the decoration value at child `j`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- The label of a dart is the decoration value at the node of its position. -/
theorem bondIndex_position (z : GNode G.tree → (Fin d → ℤ)) (x : GardenDart G) :
    bondIndex G z x =
      if h : Mole.dartPosition G x = 0 then z (G.molecule.atom x).toNode
      else z ((G.molecule.atom x).child ((Mole.dartPosition G x).pred h)) := by
  rcases x with ⟨c, b⟩ | ℓ
  · cases b
    · simp [bondIndex, Mole.dartPosition, Garden.molecule]
    · have h : (Mole.dartPosition G (Sum.inl (c, true))) ≠ 0 := by
        simp [Mole.dartPosition]
      rw [dif_neg h]
      simp only [bondIndex, Garden.molecule, Mole.dartPosition, Fin.pred_succ]
      exact congrArg z (Mole.parent_child_eq_node c.1.toNode c.2).symm
  · have h : (Mole.dartPosition G (Sum.inr ℓ)) ≠ 0 := by
      simp [Mole.dartPosition]
    rw [dif_neg h]
    simp only [bondIndex, Garden.molecule, Mole.dartPosition, Fin.pred_succ]
    exact congrArg z (Mole.parent_child_eq_node ℓ.1.toNode ℓ.2.2.1).symm

/-- At an atom of degree four every position carries a dart. -/
theorem exists_dart_at_position (a : GBranch G.tree) (hdeg : G.molecule.deg a = 4) (j : Fin 4) :
    ∃ x, G.molecule.atom x = a ∧ Mole.dartPosition G x = j := by
  classical
  have hinj : Function.Injective (fun x : {x : GardenDart G // x ∈ G.molecule.dartsAt a} =>
      Mole.dartPosition G x.1) := by
    intro x y hxy
    apply Subtype.ext
    apply Mole.atom_position_injective G
    apply Prod.ext
    · exact ((Mole.mem_dartsAt G.molecule a x.1).mp x.2).trans ((Mole.mem_dartsAt G.molecule a y.1).mp y.2).symm
    · exact hxy
  have hcard : Fintype.card {x : GardenDart G // x ∈ G.molecule.dartsAt a} = Fintype.card (Fin 4) := by
    simp only [Fintype.card_coe, Fintype.card_fin]
    exact hdeg
  have hsurj := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩ |>.2
  obtain ⟨x, hx⟩ := hsurj j
  exact ⟨x.1, (Mole.mem_dartsAt G.molecule a x.1).mp x.2, hx⟩

end WaveTurbulence.LadderDecay
