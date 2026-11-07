/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw5Clock
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand

/-! # K^T twist invariance, regional leaf pairs (V5 Step 4b, step 3, part 6) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) (hG : G.IsPlain)

/-- The pair bijection of the unit twist. -/
@[expose] noncomputable def tp : SourcePair G ≃ SourcePair (unitTwistGarden G P) :=
  sourcePairEquiv hG (unitTwistGarden_plain G P hG) (eL P) (fun l => (unitTwistGarden_pair G P l).symm)

variable {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)

include hB hCL in
theorem tp_first (p : SourcePair G) (hp : p ∈ clRegionalPairs hG T) :
    (tp P hG p).firstLeaf (unitTwistGarden_plain G P hG) = eL P (p.firstLeaf hG) ∧
    (tp P hG p).secondLeaf (unitTwistGarden_plain G P hG) = eL P (p.secondLeaf hG) := by
  have hint := (mem_clRegionalPairs G).mp hp
  have h1 : p.firstLeaf hG ≠ P.retained := fun h => not_internal_retained P hB hCL (h ▸ hint)
  have h2 : p.firstLeaf hG ≠ G.pair P.retained := fun h => not_internal_pair P hB hCL (h ▸ hint)
  have hs : nodeSign (unitTwistGarden G P).sig (eL P (p.firstLeaf hG)).1 = 1 := by
    have := coreLeafEquiv_sign G P (p.firstLeaf hG)
    simp only [coreLeafMultiplier, h1, h2, or_self, ite_false, one_mul] at this
    exact this.trans (sourcePair_first_sign G hG p)
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_pos (unitTwistGarden G P) (unitTwistGarden_plain G P hG) _ hs
  rw [hpe]
  refine ⟨hf, ?_⟩
  rw [hsec]
  exact (unitTwistGarden_pair G P (p.firstLeaf hG)).trans (congrArg (eL P) (pair_first_eq_second hG p))

end WaveTurbulence.VineEstS4
