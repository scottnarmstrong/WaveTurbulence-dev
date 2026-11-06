/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainMol
public import WaveTurbulence.Foundations.Spine.ChainDec
public import WaveTurbulence.Foundations.Spine.ChainGamma
public import WaveTurbulence.Foundations.Spine.LadderBridge
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
/-! # The ladder chart for a garden molecule (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- The additive hom `n ↦ n / L`. -/
noncomputable def latticeHom {d : ℕ} (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp [latticePoint]
  map_add' a b := by ext j; simp [latticePoint, add_div]

@[simp] lemma latticeHom_apply {d : ℕ} (L : ℝ) (n : Fin d → ℤ) : latticeHom L n = latticePoint L n := rfl

/-- The chart context of a ladder in a garden molecule. -/
noncomputable def gardenCtx {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree}
    (h : G.molecule.IsLadder u v) : LadderDarts.Ctx G.molecule u v where
  LD := Classical.choice (exists_ladderDarts G.molecule h)
  hinj := h.2.1
  hmol := Mole.garden_isMolecule G
  hdeg := Mole.garden_molecule_deg_le_four G
  hat_u := fun j => (h.2.2.1 j).1
  hat_v := fun j => (h.2.2.1 j).2


namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree}
  (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma deg_u (i : Fin n) : G.molecule.deg (u (LadderDarts.ir i)) = 4 := by
  rw [Molecule.deg, C.dartsAt_u, Finset.card_image_of_injective _ (C.LD.uDart_injective C.hinj i)]
  simp

include C in
lemma deg_v (i : Fin n) : G.molecule.deg (v (LadderDarts.ir i)) = 4 := by
  rw [Molecule.deg, C.dartsAt_v, Finset.card_image_of_injective _ (C.LD.vDart_injective C.hinj i)]
  simp

/-- The interior conservation laws of a molecule decoration, in integer form. -/
theorem interior_cons (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (k : DecLab L base roots hP) :
    (∀ i, ∑ j, sgn G.molecule (C.LD.uDart i j) • k.1 (C.LD.uDart i j) = 0) ∧
    (∀ i, ∑ j, sgn G.molecule (C.LD.vDart i j) • k.1 (C.LD.vDart i j) = 0) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact int_conservation (u (LadderDarts.ir i)) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)
      (C.out_count _ (C.hat_u _) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)) hL base k.1
      (Mole.gardenSource G hP (rootVec L base roots))
      (gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_u i)) k.2.2 (C.hat_u _)
  · exact int_conservation (v (LadderDarts.ir i)) _ (C.LD.vDart_injective C.hinj i) (C.dartsAt_v i)
      (C.out_count _ (C.hat_v _) _ (C.LD.vDart_injective C.hinj i) (C.dartsAt_v i)) hL base k.1
      (Mole.gardenSource G hP (rootVec L base roots))
      (gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_v i)) k.2.2 (C.hat_v _)

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
