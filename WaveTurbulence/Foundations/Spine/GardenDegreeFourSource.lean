/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenBoundarySource
/-! Degree-four atoms have zero boundary charge in the actual garden-to-molecule correspondence. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence.Mole

theorem gardenSource_eq_zero_of_deg_four {w : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (G : Garden w) (hp : G.IsPlain) (n : Fin w → E) (v : GBranch G.tree)
    (hdeg : G.molecule.deg v = 4) : gardenSource G hp n v = 0 := by
  classical
  let I := {x : GardenDart G // x ∈ G.molecule.dartsAt v}
  let f : I → Fin 4 := fun x => dartPosition G x.1
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply atom_position_injective G
    apply Prod.ext
    · exact ((mem_dartsAt G.molecule v x.1).mp x.2).trans
        ((mem_dartsAt G.molecule v y.1).mp y.2).symm
    · exact hxy
  have hcard : Fintype.card I = Fintype.card (Fin 4) := by
    simpa only [I, Fintype.card_coe, Fintype.card_fin, Molecule.deg] using hdeg
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).2
  unfold gardenSource slotSum
  apply neg_eq_zero.mpr
  apply sum_eq_zero
  intro i _
  obtain ⟨x, hxi⟩ := hsurj i
  have ha : G.molecule.atom x.1 = v := (mem_dartsAt G.molecule v x.1).mp x.2
  have hs : slotNode G v i = dartNode G x.1 := by
    have hpos : dartPosition G x.1 = i := hxi
    have he := congrArg₂ (slotNode G) ha hpos
    exact he.symm.trans (slotNode_dart G x.1)
  have he := congrFun (restrict_extendLabels G hp n (fun _ => (0 : E)) (fun _ => rfl)) x.1
  change extendLabels G hp n (fun _ => (0 : E)) (dartNode G x.1) = 0 at he
  rw [hs, he, smul_zero]

end WaveTurbulence.LGSpine
