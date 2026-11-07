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

/-- TARGET L1938: every block has a gap at each of its joints (existence). -/
theorem blockGap_exists {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : ∃ r, M.IsBlockGap L w κ S a r := by
  obtain ⟨_, ha, hb, _, ho1, hi1, _⟩ := hB
  have h1 : (((M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = true)).Nonempty :=
    Finset.card_pos.mp (by unfold Molecule.outIn at ho1; omega)
  have h2 : (((M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = false)).Nonempty :=
    Finset.card_pos.mp (by unfold Molecule.inIn at hi1; omega)
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  obtain ⟨hx1, hx2, hx3⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy1, hy2, hy3⟩ := Finset.mem_filter.mp hy
  exact ⟨Molecule.gapAt L w κ x y, x, y, (Mole.mem_dartsAt M a x).mp hx1,
    (Mole.mem_dartsAt M a y).mp hy1, hx2, hy2, hx3, hy3, rfl⟩

/-- The gap of a block at a joint is unique. -/
theorem blockGap_unique {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hr' : M.IsBlockGap L w κ S a r') : r = r' :=
  Vine.blockGap_unique M hB hr hr'

/-- **Gap identity from (decmole1)** (TARGET L1938-L1939): for a decoration with parameters
`(c_v)`, the gap `r` of a block at the joint `a` equals `c_a` minus the signed sum of the vectors of the
bonds joining `a` to atoms outside the block; it is a function of the vectors `k_{ℓ*}` of those bonds. -/
theorem blockGap_external {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ) {r : Mom d}
    (hr : M.IsBlockGap L w κ S a r) :
    r = c a - ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.InGroup S x),
      M.dartSign x • Molecule.kvec L w κ x := by
  have hflow := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr
  have hsum := hκ.2 a (hB.1 hB.2.1)
  have hsplit := Finset.sum_filter_add_sum_filter_not (M.dartsAt a) (M.InGroup S)
    (fun x => M.dartSign x • Molecule.kvec L w κ x)
  rw [hsum] at hsplit
  rw [hflow]
  unfold Vine.groupFlow
  rw [← hsplit]
  abel

/-- TARGET L1938: the gaps of a decorated block at its two joints are opposite, so
`k_{ℓ₁} - k_{ℓ₂} = ±(k_{ℓ₃} - k_{ℓ₄})`; `c_v = 0` at degree-four atoms is the decoration axiom. -/
theorem blockGap_opposite (hM : M.IsMolecule) {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ S b r') : r = -r' := by
  have hk (x : D) : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec, hκ.1 x]
  exact Vine.block_gaps_neg M hM hB (Molecule.kvec L w κ) hk
    (fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)) hr hr'

/-- Both joint gaps of a decorated block have the same kind (ZG, SG or LG). -/
theorem blockGap_kind_eq (hM : M.IsMolecule) {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    {L γ η : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ S b r') :
    Molecule.gapKind L γ η r = Molecule.gapKind L γ η r' := by
  rw [blockGap_opposite hM hB hκ hc hr hr', Vine.gapKind_neg]

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

/-- TARGET L1939: the gap of a hyper-block is by definition the gap of its adjoint block; hence it is
unique, and it is the gap at either joint of the adjoint. -/
theorem hyperGap_unique {S : Finset V} {a b : V} (R : Vine.HyperLikeRealization M S a b) {L : ℝ}
    {w : Mom d} {κ : D → (Fin d → ℤ)} {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : R.IsGap L w κ r') :
    r = r' := Vine.HyperLikeRealization.gap_unique R L w κ hr hr'

/-- Every vine-like object (VC, HV or HVC) has a gap; it is the gap of its block, resp. adjoint. -/
theorem vineLike_gap_exists {S : Finset V} {a b : V} (P : Vine.VineLikeObject M S a b) (L : ℝ)
    (w : Mom d) (κ : D → (Fin d → ℤ)) : ∃ r, P.IsGap L w κ r := by
  cases P with
  | vc h => exact blockGap_exists h.1 L w κ
  | hyper R => exact blockGap_exists R.adjoint.1 L w (fun x => κ x.1)

/-- SG, LG and ZG are exclusive and exhaustive (TARGET L1941), for nonnegative `L`. -/
theorem gapKind_trichotomy (L γ η : ℝ) (hL : 0 ≤ L) (r : Mom d) :
    (r = 0 ∧ Molecule.gapKind L γ η r = .ZG) ∨
    (r ≠ 0 ∧ ‖r‖ ≤ L ^ (-γ + η) ∧ Molecule.gapKind L γ η r = .SG) ∨
    (L ^ (-γ + η) < ‖r‖ ∧ Molecule.gapKind L γ η r = .LG) := by
  by_cases h0 : r = 0
  · exact Or.inl ⟨h0, (Vine.gapKind_eq_ZG_iff L γ η r).mpr h0⟩
  · by_cases hb : ‖r‖ ≤ L ^ (-γ + η)
    · exact Or.inr (Or.inl ⟨h0, hb, (Vine.gapKind_eq_SG_iff L γ η r).mpr ⟨h0, hb⟩⟩)
    · exact Or.inr (Or.inr ⟨not_le.mp hb, (Vine.gapKind_eq_LG_iff L γ η hL r).mpr (not_le.mp hb)⟩)

end WaveTurbulence.Stage1
