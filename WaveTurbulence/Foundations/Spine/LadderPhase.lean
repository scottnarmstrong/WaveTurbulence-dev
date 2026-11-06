/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderCtx
public import WaveTurbulence.Foundations.Spine.LadderTime
/-! # Phases of the ladder kernel in chart coordinates (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

lemma ext_eq_coset (hP : G.IsPlain) (L : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) :
    Mole.extendLabels G hP (rootVec L base roots) (Molecule.kvec L base (bondIndex G z.1)) =
      cosetDecoration G L base z.1 := by
  have hrest : Mole.restrictLabels G (fun a => base + latticePoint L (z.1 a)) =
      Molecule.kvec L base (bondIndex G z.1) := by
    funext x; rw [bondIndex_eq_restrict]; rfl
  rw [← hrest]
  exact Mole.extend_restrictLabels G hP (rootVec L base roots) _ (fun i => by rw [z.2.2.1 i]; rfl)
    (fun l => by simp only [z.2.1.2 l])

/-- The exponent of the ladder phase is `-Γ_a` up to the decoration-independent source. -/
theorem phase_exponent (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (a : GBranch G.tree) :
    ((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ)) * omegaNode G (cosetDecoration G L base z.1) a =
      -G.molecule.Gamma L base (bondIndex G z.1) a +
        Mole.gardenSource G hP (fun i => ‖rootVec L base roots i‖ ^ 2) a := by
  have hn : Mole.RootPairCompatible G (rootVec L base roots) :=
    Mole.rootPairCompatible_of_labels G _ (fun a => base + latticePoint L (z.1 a))
      (fun i => by rw [z.2.2.1 i]; rfl) (isDecoration_coset L base z.2.1).2
  have hk : G.molecule.IsDecoration L base (Mole.gardenSource G hP (rootVec L base roots))
      (bondIndex G z.1) := by
    rw [bondIndex_eq_restrict]
    exact Mole.moleculeDecoration_of_garden G hP (rootVec L base roots) hL base z.1
      (isDecoration_coset L base z.2.1) (fun i => by rw [z.2.2.1 i]; rfl)
  have := Mole.garden_molecule_Gamma G hP (rootVec L base roots) hn L base (bondIndex G z.1) hk a
  simp only at this
  rw [ext_eq_coset hP L base roots z] at this
  linarith

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree}
  (C : LadderDarts.Ctx G.molecule u v)

lemma gamma_u (L : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : ∀ x, κ (G.molecule.mate x) = κ x) (i : Fin n) :
    G.molecule.Gamma L base κ (u (LadderDarts.ir i)) =
      C.signs.gammaU (latticeHom L) base (C.chainOf κ) i := by
  unfold Molecule.Gamma ChainSigns.gammaU
  rw [C.sum_dartsAt_u i]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dartSign_eq_sgn, C.uSlot_chainOf κ hκ]
  rfl

lemma gamma_v (L : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : ∀ x, κ (G.molecule.mate x) = κ x) (i : Fin n) :
    G.molecule.Gamma L base κ (v (LadderDarts.ir i)) =
      C.signs.gammaV (latticeHom L) base (C.chainOf κ) i := by
  unfold Molecule.Gamma ChainSigns.gammaV
  rw [C.sum_dartsAt_v i]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dartSign_eq_sgn, C.sgn_vDart, C.vSlot_chainOf κ hκ]
  simp [signs, Molecule.kvec]


/-- The molecule decoration of a garden decoration. -/
noncomputable def decOf (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) : DecLab L base roots hP :=
  ⟨bondIndex G z.1, by
    rw [bondIndex_eq_restrict]
    exact Mole.moleculeDecoration_of_garden G hP (rootVec L base roots) hL base z.1
      (isDecoration_coset L base z.2.1) (fun i => by rw [z.2.2.1 i]; rfl)⟩

lemma isSol_decOf (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) :
    C.signs.IsSol (C.chainOf (decOf hP hL base roots z).1) :=
  C.isSol_chainOf _ (decOf hP hL base roots z).2.1
    (C.interior_cons hP hL base roots _).1 (C.interior_cons hP hL base roots _).2

/-- Interior rung phases at the u-atom. -/
theorem phase_u (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (i : Fin n) :
    ((((G.sign (u (LadderDarts.ir i)).toNode : ℤˣ) : ℤ) : ℝ)) *
        omegaNode G (cosetDecoration G L base z.1) (u (LadderDarts.ir i)) =
      -(2 * inner ℝ (latticePoint L (C.signs.pairs (C.chainOf (bondIndex G z.1)) i).1)
        (latticePoint L (C.signs.pairs (C.chainOf (bondIndex G z.1)) i).2)) := by
  rw [phase_exponent hP hL base roots z, gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_u i),
    add_zero, C.gamma_u L base (bondIndex G z.1) (decOf hP hL base roots z).2.1 i,
    C.signs.gammaU_eq (latticeHom L) base (C.chainOf (bondIndex G z.1)) (C.isSol_decOf hP hL base roots z) i]
  rfl

/-- Interior rung phases at the v-atom. -/
theorem phase_v (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (i : Fin n) :
    ((((G.sign (v (LadderDarts.ir i)).toNode : ℤˣ) : ℤ) : ℝ)) *
        omegaNode G (cosetDecoration G L base z.1) (v (LadderDarts.ir i)) =
      2 * inner ℝ (latticePoint L (C.signs.pairs (C.chainOf (bondIndex G z.1)) i).1)
        (latticePoint L (C.signs.pairs (C.chainOf (bondIndex G z.1)) i).2) +
      2 * inner ℝ (latticePoint L (C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G z.1))) i 3 -
          C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G z.1))) i 2))
        (latticePoint L (C.signs.qrel (C.chainOf (bondIndex G z.1)) i)) +
      (((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ))) *
        ‖latticePoint L (C.signs.qrel (C.chainOf (bondIndex G z.1)) i)‖ ^ 2 := by
  rw [phase_exponent hP hL base roots z, gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_v i),
    add_zero, C.gamma_v L base (bondIndex G z.1) (decOf hP hL base roots z).2.1 i,
    C.signs.gammaV_eq (latticeHom L) base (C.chainOf (bondIndex G z.1)) (C.isSol_decOf hP hL base roots z) i]
  simp only [latticeHom_apply]
  ring

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
