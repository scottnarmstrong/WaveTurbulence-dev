/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueData1
import Mathlib.Tactic

/-!
# Outside agreement of the gardens of `F` and `F.eraseCouple q` (data level)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- The gardens of `F` and of `F.eraseCouple q` agree outside the two regions at the roots of the couple at `q`. -/
theorem data_couple_outside {S : Garden w} (F : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S) :
    (∀ z : Fin w × Path,
      ¬ InRegion (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S F.tree (q.secondLeaf hS).toNode) z →
      (z.2 ∈ ((F.garden hS).tree z.1).nodes ↔ z.2 ∈ (((F.eraseCouple q).garden hS).tree z.1).nodes)) ∧
    (∀ z : Fin w × Path,
      ¬ InRegion (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S F.tree (q.secondLeaf hS).toNode) z →
      (z.2 ∈ ((F.garden hS).tree z.1).leaves ↔ z.2 ∈ (((F.eraseCouple q).garden hS).tree z.1).leaves)) ∧
    (∀ (ℓ : GLeaf (F.garden hS).tree) (ℓ' : GLeaf ((F.eraseCouple q).garden hS).tree),
      ¬ InRegion (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S F.tree (q.secondLeaf hS).toNode) ℓ.1 → ℓ.1 = ℓ'.1 →
      ((F.garden hS).pair ℓ).1 = (((F.eraseCouple q).garden hS).pair ℓ').1) := by
  by_cases hq : F.couple q = .triv
  · rw [F.eraseCouple_eq_self q hq]
    refine ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun ℓ ℓ' _ he => ?_⟩
    have : ℓ = ℓ' := Subtype.ext he
    rw [this]
  · have hd := F.garden_decodes hS
    have hc := F.eraseCouple_collapse_decodes hS hd q hq
    have hE := (F.eraseCouple q).garden_decodes hS
    have e : (F.eraseCouple q).garden hS =
        collapseCoupleGarden (F.decoded_couple_isSubCouple hS hd q) :=
      rawOfGarden_injective_plain hE.1 hc.1 (hE.2.symm.trans hc.2)
    exact couple_outside_facts (F.garden hS) (F.decoded_couple_isSubCouple hS hd q) _ e

end WaveTurbulence.Stage1
