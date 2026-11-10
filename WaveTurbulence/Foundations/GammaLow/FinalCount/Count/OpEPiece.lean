/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Pair33Count
public import WaveTurbulence.Foundations.FinalCount.OpCChain
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Boundary
public import WaveTurbulence.Foundations.CountLemmas.LowPairTarget
import Mathlib.Tactic

/-! # Operation (d)+(e) at `0 < γ ≤ 1/2`: the removed system (packet L6-COUNT, item D; M2 Lemma 4.3)

DH23 (opere) L1869–L1871 at `γ ≤ 1/2` (M2 Lemma 4.3, F-M2-2; REF-M2 §2.4). The removed part `S = C ∪ {p, q}` is a
*theta chain*: `p ≠ q` joined by exactly two bonds (darts `a, b` at `p`) and by a chain `C = S ∖ {p, q}` of atoms with
in = out = 1, entered from `p` by `z₁` and from `q` by `z₂`. In the removed molecule (`IsThetaChain`, the piece
`𝕄[S]`) `p` and `q` have degree three.

**The count** (`opE_piece_count`). With `τ = δ⁻¹L^{−2γ}` and `R = k_{z₁} − k_{z₂}` (fixed by the charges of the chain:
`chain_diff_eq`), the decorations of the piece with fixed parameters number at most
`C δ⁻¹ L^{2(d−γ)} · min(1, τ/ρ)` when `|R| ≥ ρ`, `ρ ≤ 1`. This is M2's count: the unknowns are `k_a, k_b, k_{z₁}` (the
chain is determined by `k_{z₁}`, `chain_agree`); the conservation law at `p` (no three equal signs) normalizes, by the
identity of Lemma 2.3(2) (`normTuple_inner`, main's A23HalfReparam), to two free vectors `x, y` with `|x·y − α| ≤ τ`;
the sum of the energy windows at `p` and `q` is `±(2R·k_{z₁} − |R|²)`, i.e. `|R·ξ − β'| ≤ τ` with `ξ ∈ {y, x + y}`.
Lemma 2.1(ii) is main's `exists_low_pair_selector_bound` (uncapped strip, `τL ≥ 1`, i.e. M2's volume regime (V) at
`γ ≤ 1/2`) and Lemma 2.1(i) is `coupledPair_baseline_bound`.

* `IsThetaChain`: the shape of the removed system.
* `IsThetaChain.cross_chain`, `chain_diff_eq`, `IsThetaChain.decoration_eq`: the chain's crossing darts, the fixed
  difference `k_{z₁} − k_{z₂}`, and the determination of a decoration by `k_a, k_b, k_{z₁}`.
* `opE_piece_count`: the count. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The removed system of operation (d)+(e)** (M2 Lemma 4.3): `p ≠ q` with exactly the darts `a, b, z₁` at `p` and
`mate a, mate b, z₂` at `q` (so `a, b` are the two bonds `p = q`); no three equal signs at `p`; the chain
`M.atoms ∖ {p, q}` (in = out = 1, connected) is entered by `z₁` from `p` and by `z₂` from `q`, in one direction
(`out z₁ ≠ out z₂`). -/
structure IsThetaChain (M : Molecule V D) (p q : V) (a b z₁ z₂ : D) : Prop where
  hp : p ∈ M.atoms
  hq : q ∈ M.atoms
  hpq : p ≠ q
  hab : a ≠ b
  haz : a ≠ z₁
  hbz : b ≠ z₁
  starp : M.dartsAt p = {a, b, z₁}
  hmab : M.mate a ≠ M.mate b
  hmaz : M.mate a ≠ z₂
  hmbz : M.mate b ≠ z₂
  starq : M.dartsAt q = {M.mate a, M.mate b, z₂}
  signs : ¬ (M.out a = M.out b ∧ M.out b = M.out z₁)
  dir : M.out z₁ ≠ M.out z₂
  z₁in : M.atom (M.mate z₁) ∈ M.atoms \ {p, q}
  z₂in : M.atom (M.mate z₂) ∈ M.atoms \ {p, q}
  chain : ∀ v ∈ M.atoms \ {p, q}, M.outdeg v = 1 ∧ M.indeg v = 1
  conn : ∀ u ∈ M.atoms \ {p, q}, ∀ v ∈ M.atoms \ {p, q}, (piece M (M.atoms \ {p, q})).SameComponent u v

namespace IsThetaChain
variable {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} (h : IsThetaChain M p q a b z₁ z₂)
include h

end IsThetaChain

end

/-- The two counts of a coupled pair set in the volume regime: `≤ C δ⁻¹ L^{2(d−γ)} min(1, τ/ρ)` (M2 Lemma 2.1). -/
theorem coupledPair_vol_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ ax ay r : Mom d, ρ ≤ ‖r‖ → ∀ α β : ℝ, ∀ ξsel : Fin 3,
        (coupledPairSet L ax ay r α β (δ⁻¹ * L ^ (-2 * γ)) ξsel).Finite ∧
        ((coupledPairSet L ax ay r α β (δ⁻¹ * L ^ (-2 * γ)) ξsel).ncard : ℝ) ≤
          C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := by
  obtain ⟨Cb, Lb, hCb, hbase⟩ := coupledPair_baseline_bound d hd γ ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨Cl, hCl, hstrip⟩ := exists_low_pair_selector_bound d hd 1 le_rfl
  refine ⟨Cb + Cl, max Lb 1, by positivity, ?_⟩
  intro L hL δ hδ ρ hρ hρ1 ax ay r hr α β ξsel
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
  set Vv := δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) with hVv
  have hτ0 : 0 < τ := by have := hδ.1; positivity
  have hVv0 : 0 ≤ Vv := by have := hδ.1; positivity
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hτL : 1 ≤ τ * L := by
    have hid : τ * L = δ⁻¹ * L ^ (1 - 2 * γ) := by
      simpa only [Real.rpow_one] using bandwidth_mul_rpow hLp δ γ 1
    rw [hid]
    exact one_le_mul_of_one_le_of_one_le hδi (Real.one_le_rpow hL1 (by linarith only [hγ.2]))
  have hVeq : τ * L ^ (2 * d) = Vv := by
    rw [show L ^ (2 * d) = L ^ (2 * (d : ℝ)) by norm_cast, bandwidth_mul_rpow hLp]
    congr 2; ring
  have hf := finite_coupledPairSet hLp ax ay r α β τ ξsel
  refine ⟨hf, ?_⟩
  have hb : ((coupledPairSet L ax ay r α β τ ξsel).ncard : ℝ) ≤ Cb * Vv := by
    have := hbase L ((le_max_left _ _).trans hL) δ hδ ax ay r α β ξsel
    rw [hVv, ← mul_assoc]; exact this
  have hs := hstrip L τ ρ hL1 hτL hρ hρ1 ax ay r α β (by rw [inv_one, one_mul]; exact hr) ξsel hf.toFinset
    (fun q hq => hf.mem_toFinset.mp hq)
  have hs' : ((coupledPairSet L ax ay r α β τ ξsel).ncard : ℝ) ≤ Cl * (Vv * (τ / ρ)) := by
    rw [Set.ncard_eq_toFinset_card _ hf]
    have hid : τ ^ 2 * L ^ (2 * d) / ρ = Vv * (τ / ρ) := by rw [← hVeq]; ring
    rw [← hid]; exact hs
  rcases le_total 1 (τ / ρ) with h1 | h1
  · rw [min_eq_left h1, mul_one]
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hVv0)
  · rw [min_eq_right h1]
    have : 0 ≤ Vv * (τ / ρ) := by positivity
    calc _ ≤ Cl * (Vv * (τ / ρ)) := hs'
      _ ≤ (Cb + Cl) * (Vv * (τ / ρ)) := mul_le_mul_of_nonneg_right (by linarith) this
      _ = _ := by ring

end WaveTurbulence.GammaLow.FinalCount.Count
