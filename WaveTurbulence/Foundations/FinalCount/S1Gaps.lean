/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Basic
public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
public import WaveTurbulence.Foundations.Molecule.VineGapKinds
public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
public import WaveTurbulence.Foundations.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.Molecule.VineLikeGapObjects
import Mathlib.Tactic

/-!
# TARGET defdiff (L1938-L1941; DH23 Def 8.3): gaps of blocks and hyper-blocks

The definitions are the owner-pinned B2 definitions `Molecule.IsBlockGap`, `Molecule.gapAt`,
`Molecule.gapKind` (ZG: `r = 0`; SG: `0 < ‖r‖ ≤ L^(-γ+η)`; LG: `‖r‖ > L^(-γ+η)`) and
`Molecule.IsLadderGap`; here we prove the claims made in the source text of the definition:

* the gap of a block exists and is unique at each joint;
* the gap identity from (decmole1): `r = c_a - ∑_{external darts at a} ζ k` (the gap is a function of
  the vectors `k_{ℓ*}` of the bonds joining the joint to atoms outside the block);
* the two joint gaps of a decorated block are opposite (`k_{ℓ₁}-k_{ℓ₂} = ±(k_{ℓ₃}-k_{ℓ₄})`);
* every ingredient of a concatenated block has the gap of the whole block;
* the gap of a hyper-block is the gap of its designated adjoint, hence unique.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- TARGET L1939: if `B` is concatenated by blocks `B_j`, every ingredient `A` has the gap of `B`
(up to the sign recorded by its two joints). -/
theorem ingredient_gap_eq (hM : M.IsMolecule) {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : Vine.ChainIngredient M U a b n A x y) (hU : M.IsBlock U a b) {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) {rU rx ry : Mom d}
    (hrU : M.IsBlockGap L w κ U a rU) (hrx : M.IsBlockGap L w κ A x rx)
    (hry : M.IsBlockGap L w κ A y ry) : rx = rU ∧ ry = -rU := by
  have hk (z : D) : Molecule.kvec L w κ (M.mate z) = Molecule.kvec L w κ z := by
    simp only [Molecule.kvec, hκ.1 z]
  have hcc : ∀ v ∈ M.atoms, M.deg v = 4 →
      ∑ z ∈ M.dartsAt v, M.dartSign z • Molecule.kvec L w κ z = 0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)
  obtain ⟨h1, h2⟩ := Vine.chainIngredient_flow_eq M hM (Molecule.kvec L w κ) hk hcc h hU
  obtain ⟨hAB, _, _⟩ := Vine.chainIngredient_spec h
  have hAblock : M.IsBlock A x y := by
    obtain ⟨_, ⟨Y, hY⟩, _⟩ := Vine.chainIngredient_spec h
    exact hY.1
  have e1 := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hAblock).1 hrx
  have e2 := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hAblock).2 hry
  have e3 := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hU).1 hrU
  exact ⟨by rw [e1, e3, h1], by rw [e2, e3, h2]⟩

end WaveTurbulence.Stage1
