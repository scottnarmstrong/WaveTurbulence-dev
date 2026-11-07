/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
import Mathlib.Tactic

/-!
# S2 REPRESENTS, vine-free case: transport of decorations along `G_sb = S`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

/-- Transport of nodes along `(stSt S σ).G = S` (no unit spliced). -/
@[expose] def nodeCast (σ : Prescription S) (h : unitBlocks S σ = []) (n : GNode (stSt S σ).G.tree) : GNode S.tree :=
  (congrArg (fun G : Garden w => GNode G.tree) (stSt_G_eq_of_unitBlocks_empty σ h)) ▸ n

theorem bondIndex_nodeCast (σ : Prescription S) (h : unitBlocks S σ = []) {d : ℕ}
    (zS : GNode S.tree → (Fin d → ℤ)) (y : GardenDart (stSt S σ).G) :
    bondIndex (stSt S σ).G (fun n => zS (nodeCast σ h n)) y = bondIndex S zS ((stSt S σ).M.od y) := by
  have key : ∀ st : SpState S, ∀ hst : st = SpState.init S, ∀ (y : GardenDart st.G),
      bondIndex st.G (fun n => zS ((congrArg (fun G : Garden w => GNode G.tree)
        (show st.G = S by rw [hst]; rfl)) ▸ n)) y = bondIndex S zS (st.M.od y) := by
    rintro st rfl y
    rfl
  exact key _ (stSt_eq_init_of_unitBlocks_empty σ h) y

open scoped Classical in
/-- The spliced gap indicator of the vine-free piece is the `σ`-restriction on skeleton decorations. -/
theorem gapIndicator_noVine (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    (h : unitBlocks S σ = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (zS : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = gapSpecification S σ) :
    splicedGapIndicator (stSt S σ).G D L γ η base (fun n => zS.1 (nodeCast σ h n)) =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base zS.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOf (G := S) hM σ L γ η base _ zS.1
    (spliced_molecule_decoration S hp hL base roots zS)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four S hp _ v hv) _
    (bondIndex_nodeCast σ h zS.1) D hD

theorem splicedEpsilon_empty {d : ℕ} (G : Garden w) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedEpsilon G ∅ z = epsDec G z := by
  unfold splicedEpsilon epsDec
  simp

end WaveTurbulence.Represents
