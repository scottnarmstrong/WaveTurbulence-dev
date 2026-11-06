/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenPos
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
/-! # Children labels of a degree-four atom as slot labels (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

lemma epsCoef_translate (n1 n2 n3 A : Fin d → ℤ) :
    epsCoef (n1 + A) (n2 + A) (n3 + A) = epsCoef n1 n2 n3 := by
  unfold epsCoef; simp

/-- The three children labels of a degree-four atom are the labels of three distinct slot darts. -/
theorem children_slots (a : GBranch G.tree) (hdeg : G.molecule.deg a = 4) (f : Fin 4 → GardenDart G)
    (hd : G.molecule.dartsAt a = univ.image f) :
    ∃ k : Fin 3 → Fin 4, Function.Injective k ∧
      ∀ (z : GNode G.tree → (Fin d → ℤ)) (j : Fin 3),
        z (a.child j) = bondIndex G z (f (k j)) := by
  have hex : ∀ j : Fin 3, ∃ s : Fin 4, G.molecule.atom (f s) = a ∧ Mole.dartPosition G (f s) = j.succ := by
    intro j
    obtain ⟨x, hxa, hxp⟩ := exists_dart_at_position a hdeg j.succ
    have hmem : x ∈ G.molecule.dartsAt a := by
      rw [Molecule.dartsAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hxa⟩
    rw [hd] at hmem
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨s, hxa, hxp⟩
  choose k hk using hex
  refine ⟨k, ?_, ?_⟩
  · intro j j' h
    have := (hk j).2
    rw [h, (hk j').2] at this
    exact Fin.succ_injective _ this.symm
  · intro z j
    rw [bondIndex_position]
    have e1 : Mole.dartPosition G (f (k j)) = j.succ := (hk j).2
    have e2 : G.molecule.atom (f (k j)) = a := (hk j).1
    have hne : Mole.dartPosition G (f (k j)) ≠ 0 := by rw [e1]; exact Fin.succ_ne_zero _
    rw [dif_neg hne]
    simp only [e1, e2, Fin.pred_succ]

/-- Every dart at an atom of degree four is a slot dart. -/
lemma slot_of_dart (a : GBranch G.tree) (f : Fin 4 → GardenDart G)
    (hd : G.molecule.dartsAt a = univ.image f) (x : GardenDart G) (hx : G.molecule.atom x = a) :
    ∃ s, f s = x := by
  have hmem : x ∈ G.molecule.dartsAt a := by
    rw [Molecule.dartsAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩
  rw [hd] at hmem
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hmem
  exact ⟨s, rfl⟩

end WaveTurbulence.LadderDecay
