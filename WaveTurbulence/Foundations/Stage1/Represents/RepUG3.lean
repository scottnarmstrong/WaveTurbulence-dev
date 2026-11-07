/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG2
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (3): the SG gap clause of `outSet` for every unit

`unitGap_of_selOf`: for a decoration `z` of a plain molecule garden `G` satisfying the prescription restriction `selOf σ`
(TARGET L1950) and every unit `u ∈ unitBlocks G σ`, the unit's boundary momenta `β i = base + latticePoint L (z (bnodes u i))`
satisfy `UnitGap L γ η β` (`β 0 ≠ β 1`, `‖β 0 - β 1‖ ≤ L^(-γ+η)`), the SG clause of `outSet`.
Route: `exists_unitSpec` (an external pair at a joint of `u`), `unitSpec_gapKind` (its gap has the kind of the designated
object, SG since `σ S = SG` and `selOf`), `extPair_nodes` (the pair sits on the boundary nodes of that joint) and the signed
block conservation to pass between the joints.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The joint of the external pair of a unit is one of its joints. -/
theorem unitSpec_joint {Sg : Finset (GBranch G.tree)} {u : CLBlock G} (hu : u ∈ (groupUnitsOf G Sg).units)
    {p : GardenDart G × GardenDart G} (hsp : UnitSpec G Sg u p) :
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom p.1 = j ∧ G.molecule.atom p.2 = j := by
  obtain ⟨j, hj, hT, hn1, hn2, hrel⟩ := hsp
  refine ⟨j, ?_, hT.1, hT.2.1⟩
  rcases hsk : (groupUnitsOf G Sg).skip with _ | sk
  · exact (hrel.2 hsk).2
  · obtain ⟨hjxy, -⟩ := hrel.1 sk hsk
    obtain ⟨hu', hL, hR⟩ := (groupUnitsOf G Sg).skip_units sk hsk
    obtain ⟨X, hX⟩ := sk.vine
    have hxy : sk.x ≠ sk.y := hX.1.2.2.2.1
    rcases hu' u hu with ⟨hat, hjn⟩ | ⟨hat, hjn⟩
    · rw [hat] at hj
      rcases hjxy with rfl | rfl
      · rcases hjn with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr h.symm
        · exact Or.inl h.symm
      · exfalso
        rcases sk.left with ⟨h0, -⟩ | ⟨-, -, -, hLA⟩
        · rw [h0] at hj; exact absurd hj (by simp)
        · have : sk.y ∈ sk.L0 ∩ sk.A := Finset.mem_inter.mpr ⟨hj, hX.1.2.2.1⟩
          rw [hLA, Finset.mem_singleton] at this
          exact hxy this.symm
    · rw [hat] at hj
      rcases hjxy with rfl | rfl
      · exfalso
        rcases sk.right with ⟨h0, -⟩ | ⟨-, -, -, hRA⟩
        · rw [h0] at hj; exact absurd hj (by simp)
        · have : sk.x ∈ sk.R0 ∩ sk.A := Finset.mem_inter.mpr ⟨hj, hX.1.2.1⟩
          rw [hRA, Finset.mem_singleton] at this
          exact hxy this
      · rcases hjn with ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl h.symm
        · exact Or.inr h.symm

/-- The arithmetic of the gap clause. -/
theorem unitGap_of_cases {d : ℕ} (L γ η : ℝ) (β : Fin 4 → Mom d) (r : Mom d)
    (hk : Molecule.gapKind L γ η r = Molecule.GapKind.SG)
    (hr : r = β 0 - β 1 ∨ r = β 1 - β 0 ∨ r = β 2 - β 3 ∨ r = β 3 - β 2)
    (hc : β 2 - β 3 = β 0 - β 1 ∨ β 2 - β 3 = β 1 - β 0) : VineB.UnitGap L γ η β := by
  unfold Molecule.gapKind at hk
  by_cases h0 : r = 0
  · rw [if_pos h0] at hk; exact absurd hk (by decide)
  rw [if_neg h0] at hk
  by_cases h1 : ‖r‖ ≤ L ^ (-γ + η)
  swap
  · rw [if_neg h1] at hk; exact absurd hk (by decide)
  have hv : β 0 - β 1 ≠ 0 ∧ ‖β 0 - β 1‖ = ‖r‖ := by
    rcases hr with h | h | h | h
    · exact ⟨h ▸ h0, by rw [h]⟩
    · exact ⟨fun h' => h0 (by rw [h, ← neg_sub, h', neg_zero]), by rw [h, norm_sub_rev]⟩
    · rcases hc with hc | hc
      · rw [hc] at h; exact ⟨h ▸ h0, by rw [h]⟩
      · rw [hc] at h; exact ⟨fun h' => h0 (by rw [h, ← neg_sub, h', neg_zero]), by rw [h, norm_sub_rev]⟩
    · rcases hc with hc | hc
      · rw [← neg_sub, hc] at h
        exact ⟨fun h' => h0 (by rw [h, h', neg_zero]), by rw [h, norm_neg]⟩
      · rw [← neg_sub, hc, neg_sub] at h
        exact ⟨h ▸ h0, by rw [h]⟩
  exact ⟨sub_ne_zero.mp hv.1, by rw [hv.2]; exact h1⟩

/-- Passing from the lower to the upper joint: `ζ (z0 - z1) = z2 - z3`, in momenta. -/
theorem boundary_diff_cases {d : ℕ} (u : CLBlock G) (L : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hz : IsDecoration G z) :
    (base + latticePoint L (z (bnodes u 2))) - (base + latticePoint L (z (bnodes u 3))) =
        (base + latticePoint L (z (bnodes u 0))) - (base + latticePoint L (z (bnodes u 1))) ∨
      (base + latticePoint L (z (bnodes u 2))) - (base + latticePoint L (z (bnodes u 3))) =
        (base + latticePoint L (z (bnodes u 1))) - (base + latticePoint L (z (bnodes u 0))) := by
  have h := block_signed_conservation u z hz
  have e1 : G.sign (bnodes u 1) = G.sign u.upper.toNode := by
    show G.sign (u.upper.child (regionOf u).excluded) = _
    rw [WaveTurbulence.Mole.child_sign_formula, if_neg (regionOf u).excluded_ne_middle]
  have e2 : G.sign (bnodes u 2) = 1 := (regionOf u).positive_sign
  have e3 : G.sign (bnodes u 3) = -1 := (regionOf u).negative_sign
  change ((G.sign u.upper.toNode : ℤˣ) : ℤ) • z (bnodes u 0) =
      ((G.sign (bnodes u 1) : ℤˣ) : ℤ) • z (bnodes u 1) + ((G.sign (bnodes u 2) : ℤˣ) : ℤ) • z (bnodes u 2) +
        ((G.sign (bnodes u 3) : ℤˣ) : ℤ) • z (bnodes u 3) at h
  rw [e1, e2, e3] at h
  have hsub : ∀ a b : Fin d → ℤ, latticePoint L (a - b) = latticePoint L a - latticePoint L b :=
    fun a b => RegRed.latticePoint_sub L a b
  have key : ∀ a b : Mom d, (base + a) - (base + b) = a - b := fun a b => by abel
  have hint : z (bnodes u 2) - z (bnodes u 3) = z (bnodes u 0) - z (bnodes u 1) ∨
      z (bnodes u 2) - z (bnodes u 3) = z (bnodes u 1) - z (bnodes u 0) := by
    rcases Int.units_eq_one_or (G.sign u.upper.toNode) with e | e
    · rw [e] at h
      simp only [Units.val_one, one_smul, Units.val_neg, neg_smul] at h
      left
      funext k
      have := congrFun h k
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at this ⊢
      omega
    · rw [e] at h
      simp only [Units.val_one, one_smul, Units.val_neg, neg_smul] at h
      right
      funext k
      have := congrFun h k
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at this ⊢
      omega
  simp only [key]
  rcases hint with h' | h'
  · left; rw [← hsub, ← hsub, h']
  · right; rw [← hsub, ← hsub, h']

end WaveTurbulence.Represents
