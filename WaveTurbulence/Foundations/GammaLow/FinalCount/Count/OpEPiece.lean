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

theorem atom_of_p {z : D} (hz : M.atom z = p) : z = a ∨ z = b ∨ z = z₁ := by
  have hm : z ∈ M.dartsAt p := (Mole.mem_dartsAt M p z).mpr hz
  rw [h.starp] at hm
  simpa using hm

theorem atom_of_q {z : D} (hz : M.atom z = q) : z = M.mate a ∨ z = M.mate b ∨ z = z₂ := by
  have hm : z ∈ M.dartsAt q := (Mole.mem_dartsAt M q z).mpr hz
  rw [h.starq] at hm
  simpa using hm

theorem atom_a : M.atom a = p := (Mole.mem_dartsAt M p a).mp (by rw [h.starp]; simp)
theorem atom_b : M.atom b = p := (Mole.mem_dartsAt M p b).mp (by rw [h.starp]; simp)
theorem atom_z₁ : M.atom z₁ = p := (Mole.mem_dartsAt M p z₁).mp (by rw [h.starp]; simp)
theorem atom_ma : M.atom (M.mate a) = q := (Mole.mem_dartsAt M q _).mp (by rw [h.starq]; simp)
theorem atom_mb : M.atom (M.mate b) = q := (Mole.mem_dartsAt M q _).mp (by rw [h.starq]; simp)
theorem atom_z₂ : M.atom z₂ = q := (Mole.mem_dartsAt M q z₂).mp (by rw [h.starq]; simp)

theorem chain_sub : M.atoms \ {p, q} ⊆ M.atoms := sdiff_subset

theorem mz₁_ne_mz₂ : M.mate z₁ ≠ M.mate z₂ := by
  intro he
  have : z₁ = z₂ := by have := congrArg M.mate he; rwa [M.mate_mate, M.mate_mate] at this
  exact h.hpq (by rw [← h.atom_z₁, ← h.atom_z₂, this])

/-- The chain is attached to `p, q` exactly by `mate z₁` and `mate z₂`. -/
theorem cross_chain : crossDarts M (M.atoms \ {p, q}) = {M.mate z₁, M.mate z₂} := by
  ext x
  simp only [mem_crossDarts, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hx, hmx⟩
    have hmA : M.atom (M.mate x) ∈ M.atoms := M.atom_mem _
    have hpq' : M.atom (M.mate x) = p ∨ M.atom (M.mate x) = q := by
      by_contra hne
      push Not at hne
      exact hmx (mem_sdiff.mpr ⟨hmA, by simp [hne.1, hne.2]⟩)
    have hxY := (mem_sdiff.mp hx).2
    rcases hpq' with hp' | hq'
    · rcases h.atom_of_p hp' with e | e | e
      · exact absurd (by rw [← M.mate_mate x, e, h.atom_ma] : M.atom x = q) (fun h' => hxY (by simp [h']))
      · exact absurd (by rw [← M.mate_mate x, e, h.atom_mb] : M.atom x = q) (fun h' => hxY (by simp [h']))
      · left; rw [← e, M.mate_mate]
    · rcases h.atom_of_q hq' with e | e | e
      · exact absurd (by rw [← M.mate_mate x, e, M.mate_mate, h.atom_a] : M.atom x = p)
          (fun h' => hxY (by simp [h']))
      · exact absurd (by rw [← M.mate_mate x, e, M.mate_mate, h.atom_b] : M.atom x = p)
          (fun h' => hxY (by simp [h']))
      · right; rw [← e, M.mate_mate]
  · rintro (rfl | rfl)
    · refine ⟨h.z₁in, ?_⟩
      rw [M.mate_mate, h.atom_z₁]; simp
    · refine ⟨h.z₂in, ?_⟩
      rw [M.mate_mate, h.atom_z₂]; simp

theorem dartSign_z₂ : M.dartSign z₂ = - M.dartSign z₁ := by
  unfold Molecule.dartSign
  have hd := h.dir
  cases h1 : M.out z₁ <;> cases h2 : M.out z₂ <;> simp_all

theorem dartSign_z₁_sq : M.dartSign z₁ * M.dartSign z₁ = 1 := by
  unfold Molecule.dartSign; split_ifs <;> norm_num

theorem abs_dartSign_z₁ : |M.dartSign z₁| = 1 := by
  unfold Molecule.dartSign; split_ifs <;> norm_num

/-- **The chain charge**: `s₁ (k_{z₁} − k_{z₂}) = − ∑_{C} c_v` for every decoration (`s₁` the sign of `z₁`). -/
theorem chain_sum {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ) :
    M.dartSign z₁ • (Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂) = - ∑ v ∈ M.atoms \ {p, q}, c v := by
  rw [sum_charges_eq_cross hκ h.chain_sub, h.cross_chain, sum_pair h.mz₁_ne_mz₂,
    dartSign_mate, dartSign_mate, h.dartSign_z₂]
  simp only [Molecule.kvec, hκ.1]
  rw [smul_sub, neg_add, neg_smul, neg_smul, neg_neg, neg_smul]
  abel

end IsThetaChain

/-- **The fixed chain difference**: `k_{z₁} − k_{z₂}` is the same for all decorations with the same charges. -/
theorem chain_diff_eq {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} (h : IsThetaChain M p q a b z₁ z₂) {d : ℕ}
    {L : ℝ} {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ)
    (hκ' : M.IsDecoration L 0 c κ') :
    Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂ = Molecule.kvec L 0 κ' z₁ - Molecule.kvec L 0 κ' z₂ := by
  have e := (h.chain_sum hκ).trans (h.chain_sum hκ').symm
  have hs : M.dartSign z₁ ≠ 0 := by intro h0; have := h.dartSign_z₁_sq; rw [h0] at this; norm_num at this
  exact smul_right_injective _ hs e

/-- **Determination**: a decoration is determined by its charges and its labels at `a, b, z₁`. -/
theorem IsThetaChain.decoration_eq {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} (h : IsThetaChain M p q a b z₁ z₂)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ)
    (hκ' : M.IsDecoration L 0 c κ') (ha : κ a = κ' a) (hb : κ b = κ' b) (hz : κ z₁ = κ' z₁) : κ = κ' := by
  have hag := FinalCountG8.chain_agree M h.chain_sub h.chain h.conn hL hκ hκ' (z0 := M.mate z₁) h.z₁in
    (by rw [hκ.1, hκ'.1, hz])
  funext z
  have hzA : M.atom z ∈ M.atoms := M.atom_mem z
  by_cases hzp : M.atom z = p
  · rcases h.atom_of_p hzp with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hz
  by_cases hzq : M.atom z = q
  · rcases h.atom_of_q hzq with rfl | rfl | rfl
    · rw [hκ.1, hκ'.1, ha]
    · rw [hκ.1, hκ'.1, hb]
    · have := hag (M.mate z) h.z₂in
      rwa [hκ.1, hκ'.1] at this
  exact hag z (mem_sdiff.mpr ⟨hzA, by simp [hzp, hzq]⟩)

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

/-- **The count of the removed system of operation (d)+(e)** (M2 Lemma 4.3, count; Lemma 2.1(ii)), `0 < γ ≤ 1/2`:
if every admissible decoration has `|k_{z₁} − k_{z₂}| ≥ ρ` (`0 < ρ ≤ 1`), then
`𝔈(theta chain) ≤ C δ⁻¹ L^{2(d−γ)} · min(1, δ⁻¹ L^{−2γ}/ρ)`. -/
theorem opE_piece_count (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (p q : V) (a b z₁ z₂ : D),
      IsThetaChain M p q a b z₁ z₂ → ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖) →
      ∃ n : ℕ, (n : ℝ) ≤ C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) ∧
        MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤ n := by
  obtain ⟨C, L₀, hC, hvol⟩ := coupledPair_vol_bound d hd γ hγ
  refine ⟨C, max L₀ 1, hC, ?_⟩
  intro L hL δ hδ ρ hρ hρ1 V D _ _ _ M p q a b z₁ z₂ hT Adm hAdm
  classical
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
  set B := C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (τ / ρ) with hBdef
  have hB0 : 0 ≤ B := by
    have := hδ.1
    have : 0 ≤ min 1 (τ / ρ) := le_min zero_le_one (by positivity)
    positivity
  refine ⟨⌊B⌋₊, Nat.floor_le hB0, ?_⟩
  unfold MoleProp.countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | M.IsDecoration L 0 c κ ∧ M.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ} with hA
  have hAfin : A.Finite := (Mole.finite_restricted M hLp γ δ 0 β k0).subset fun _ h => h.2.1
  rcases A.eq_empty_or_nonempty with hA0 | ⟨κ0, hκ0⟩
  · rw [hA0, Set.encard_empty]; exact bot_le
  suffices hcard : (A.ncard : ℝ) ≤ B by
    rw [← hAfin.cast_ncard_eq]
    exact_mod_cast Nat.le_floor hcard
  -- the fixed chain difference
  set Rv : Mom d := Molecule.kvec L 0 κ0 z₁ - Molecule.kvec L 0 κ0 z₂ with hRv
  have hR : ∀ κ ∈ A, latticePoint L (κ z₂) = latticePoint L (κ z₁) - Rv := by
    intro κ hκ
    have e := chain_diff_eq hT hκ.1 hκ0.1
    simp only [Molecule.kvec, zero_add] at e hRv
    rw [hRv, ← e]; abel
  have hRρ : ρ ≤ ‖Rv‖ := hAdm κ0 hκ0.2.2
  -- the energy window on `R · k_{z₁}`
  set s₁ := M.dartSign z₁ with hs₁
  set βs : ℝ := (‖Rv‖ ^ 2 + s₁ * (β p + β q)) / 2 with hβs
  have hER : ∀ κ ∈ A, |inner ℝ Rv (latticePoint L (κ z₁)) - βs| ≤ τ := by
    intro κ hκ
    have hEp := energy_of_dartsAt_triple M L γ δ hT.hp hT.hab hT.haz hT.hbz hT.starp hκ.2.1
    have hEq := energy_of_dartsAt_triple M L γ δ hT.hq hT.hmab hT.hmaz hT.hmbz hT.starq hκ.2.1
    rw [hκ.1.1 a, hκ.1.1 b, dartSign_mate, dartSign_mate, hT.dartSign_z₂, hR κ hκ] at hEq
    rw [← hs₁] at hEp hEq
    set k := latticePoint L (κ z₁)
    have hsq : ‖k - Rv‖ ^ 2 = ‖k‖ ^ 2 - 2 * inner ℝ k Rv + ‖Rv‖ ^ 2 := norm_sub_sq_real k Rv
    have hsum : |s₁ * (2 * inner ℝ Rv k - ‖Rv‖ ^ 2) - (β p + β q)| ≤ 2 * τ := by
      have e : s₁ * (2 * inner ℝ Rv k - ‖Rv‖ ^ 2) - (β p + β q) =
          (M.dartSign a * ‖latticePoint L (κ a)‖ ^ 2 + M.dartSign b * ‖latticePoint L (κ b)‖ ^ 2 +
            s₁ * ‖k‖ ^ 2 - β p) +
          (-M.dartSign a * ‖latticePoint L (κ a)‖ ^ 2 + -M.dartSign b * ‖latticePoint L (κ b)‖ ^ 2 +
            -s₁ * ‖k - Rv‖ ^ 2 - β q) := by
        rw [hsq, real_inner_comm]; ring
      rw [e]
      exact (abs_add_le _ _).trans (by linarith)
    have e2 : 2 * (inner ℝ Rv k - βs) = s₁ * (s₁ * (2 * inner ℝ Rv k - ‖Rv‖ ^ 2) - (β p + β q)) := by
      rw [hβs]; linear_combination (-(2 * inner ℝ Rv k - ‖Rv‖ ^ 2)) * hT.dartSign_z₁_sq
    have h2 : |2 * (inner ℝ Rv k - βs)| ≤ 2 * τ := by
      rw [e2, abs_mul, hT.abs_dartSign_z₁, one_mul]; exact hsum
    rw [abs_mul, abs_two] at h2
    linarith
  -- the conservation law at `p`, in integer coordinates
  set εA : Fin 3 → ℤˣ := ![sgn M a, sgn M b, sgn M z₁] with hεA
  set nA : Fin d → ℤ := doubleSign (M.out a) • κ0 a + doubleSign (M.out b) • κ0 b + doubleSign (M.out z₁) • κ0 z₁
  let nf : (D → (Fin d → ℤ)) → Fin 5 → Fin d → ℤ := fun κ => ![κ a, κ b, κ z₁, 0, 0]
  have hTup : ∀ κ ∈ A, TupleEqn L (nf κ) ![0, 1, 2] εA nA (β p) τ := by
    intro κ hκ
    have hmA := momentum_of_dartsAt_triple M L hT.hp hT.hab hT.haz hT.hbz hT.starp hκ.1
    have hm0A := momentum_of_dartsAt_triple M L hT.hp hT.hab hT.haz hT.hbz hT.starp hκ0.1
    have hEA := energy_of_dartsAt_triple M L γ δ hT.hp hT.hab hT.haz hT.hbz hT.starp hκ.2.1
    refine ⟨?_, ?_⟩
    · have key : doubleSign (M.out a) • κ a + doubleSign (M.out b) • κ b + doubleSign (M.out z₁) • κ z₁ = nA := by
        apply latticePointHom_injective hLp.ne'
        simp only [nA, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
        exact hmA.trans hm0A.symm
      simpa [Fin.sum_univ_three, nf, hεA, sgn_cast] using key
    · rw [hτ]; simpa [Fin.sum_univ_three, nf, hεA, sgn_cast_real] using hEA
  have hεc : ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) := fun ⟨h1, h2⟩ =>
    hT.signs ⟨(sgn_eq_iff M a b).mp (by simpa [hεA] using h1), (sgn_eq_iff M b z₁).mp (by simpa [hεA] using h2)⟩
  obtain ⟨s, P, Q, O, hsh, hnT⟩ := tupleEqn_normalize (d := d) εA hεc
  have hN : ∀ κ ∈ A, NormTuple L (nf κ) (![0, 1, 2] P) (![0, 1, 2] Q) (![0, 1, 2] O) (s • nA) (s * β p) τ :=
    fun κ hκ => hnT L (nf κ) _ nA (β p) τ (hTup κ hκ)
  set m := s • nA with hm
  have hnear : ∀ κ ∈ A, ∀ z, NearLattice L (k0 z) (κ z) := fun κ hκ z => by
    simpa only [NearLattice, Molecule.kvec, zero_add] using hκ.2.1.2 z
  have hinner : ∀ κ ∈ A, inner ℝ Rv (latticePoint L (κ z₁ - m)) = inner ℝ Rv (latticePoint L (κ z₁)) -
      inner ℝ Rv (latticePoint L m) := fun κ _ => by
    rw [WeylSums.latticePoint_sub_eq, inner_sub_right]
  have hnf0 : ∀ κ, nf κ 0 = κ a := fun κ => rfl
  have hnf1 : ∀ κ, nf κ 1 = κ b := fun κ => rfl
  have hnf2 : ∀ κ, nf κ 2 = κ z₁ := fun κ => rfl
  set α₀ : ℝ := (‖latticePoint L m‖ ^ 2 - s * β p) / 2 with hα₀
  set β₀ : ℝ := βs - inner ℝ Rv (latticePoint L m) with hβ₀
  have hz1 : ∀ κ ∈ A, |inner ℝ Rv (latticePoint L (κ z₁ - m)) - β₀| ≤ τ := by
    intro κ hκ
    rw [hinner κ hκ, hβ₀, show inner ℝ Rv (latticePoint L (κ z₁)) - inner ℝ Rv (latticePoint L m) -
      (βs - inner ℝ Rv (latticePoint L m)) = inner ℝ Rv (latticePoint L (κ z₁)) - βs by ring]
    exact hER κ hκ
  -- the three normalized shapes
  rcases hsh with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- `k_b + k_{z₁} − k_a = m`: `x = k_b − m`, `y = k_{z₁} − m`, `ξ = y`
    have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 1 2 0 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hvol L hLL δ hδ ρ hρ hρ1 (k0 b - latticePoint L m) (k0 z₁ - latticePoint L m) Rv hRρ
      α₀ β₀ 1
    have hmem : ∀ κ ∈ A, (κ b - m, κ z₁ - m) ∈
        coupledPairSet L (k0 b - latticePoint L m) (k0 z₁ - latticePoint L m) Rv α₀ β₀ τ 1 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf1, hnf2] at hi
      exact ⟨nearLattice_sub m (hnear κ hκ b), nearLattice_sub m (hnear κ hκ z₁), hi, hz1 κ hκ⟩
    have hinj : Set.InjOn (fun κ : D → (Fin d → ℤ) => (κ b - m, κ z₁ - m)) A := by
      intro κ hκ κ' hκ' he
      simp only [Prod.mk.injEq, sub_left_inj] at he
      have e1 := (hN' κ hκ).1
      have e2 := (hN' κ' hκ').1
      rw [hnf0, hnf1, hnf2] at e1 e2
      have h0 : κ a = κ' a := by
        have i1 : κ a = κ b + κ z₁ - m := by rw [← e1]; abel
        have i2 : κ' a = κ' b + κ' z₁ - m := by rw [← e2]; abel
        rw [i1, i2, he.1, he.2]
      exact hT.decoration_eq hLp.ne' hκ.1 hκ'.1 h0 he.1 he.2
    exact (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn _ hmem hinj hfin)).trans hcnt
  · -- `k_a + k_{z₁} − k_b = m`: `x = k_a − m`, `y = k_{z₁} − m`, `ξ = y`
    have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 0 2 1 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hvol L hLL δ hδ ρ hρ hρ1 (k0 a - latticePoint L m) (k0 z₁ - latticePoint L m) Rv hRρ
      α₀ β₀ 1
    have hmem : ∀ κ ∈ A, (κ a - m, κ z₁ - m) ∈
        coupledPairSet L (k0 a - latticePoint L m) (k0 z₁ - latticePoint L m) Rv α₀ β₀ τ 1 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf0, hnf2] at hi
      exact ⟨nearLattice_sub m (hnear κ hκ a), nearLattice_sub m (hnear κ hκ z₁), hi, hz1 κ hκ⟩
    have hinj : Set.InjOn (fun κ : D → (Fin d → ℤ) => (κ a - m, κ z₁ - m)) A := by
      intro κ hκ κ' hκ' he
      simp only [Prod.mk.injEq, sub_left_inj] at he
      have e1 := (hN' κ hκ).1
      have e2 := (hN' κ' hκ').1
      rw [hnf0, hnf1, hnf2] at e1 e2
      have h1 : κ b = κ' b := by
        have i1 : κ b = κ a + κ z₁ - m := by rw [← e1]; abel
        have i2 : κ' b = κ' a + κ' z₁ - m := by rw [← e2]; abel
        rw [i1, i2, he.1, he.2]
      exact hT.decoration_eq hLp.ne' hκ.1 hκ'.1 he.1 h1 he.2
    exact (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn _ hmem hinj hfin)).trans hcnt
  · -- `k_a + k_b − k_{z₁} = m`: `x = k_a − m`, `y = k_b − m`, `ξ = x + y`
    have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 0 1 2 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hvol L hLL δ hδ ρ hρ hρ1 (k0 a - latticePoint L m) (k0 b - latticePoint L m) Rv hRρ
      α₀ β₀ 2
    have hez : ∀ κ ∈ A, κ z₁ = κ a + κ b - m := by
      intro κ hκ
      have e1 := (hN' κ hκ).1
      rw [hnf0, hnf1, hnf2] at e1
      rw [← e1]; abel
    have hmem : ∀ κ ∈ A, (κ a - m, κ b - m) ∈
        coupledPairSet L (k0 a - latticePoint L m) (k0 b - latticePoint L m) Rv α₀ β₀ τ 2 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf0, hnf1] at hi
      have h4 : |inner ℝ Rv (latticePoint L (κ a - m) + latticePoint L (κ b - m)) - β₀| ≤ τ := by
        rw [← WeylSums.latticePoint_add_eq, show κ a - m + (κ b - m) = κ z₁ - m by rw [hez κ hκ]; abel]
        exact hz1 κ hκ
      exact ⟨nearLattice_sub m (hnear κ hκ a), nearLattice_sub m (hnear κ hκ b), hi, h4⟩
    have hinj : Set.InjOn (fun κ : D → (Fin d → ℤ) => (κ a - m, κ b - m)) A := by
      intro κ hκ κ' hκ' he
      simp only [Prod.mk.injEq, sub_left_inj] at he
      have h2 : κ z₁ = κ' z₁ := by rw [hez κ hκ, hez κ' hκ', he.1, he.2]
      exact hT.decoration_eq hLp.ne' hκ.1 hκ'.1 he.1 he.2 h2
    exact (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn _ hmem hinj hfin)).trans hcnt

end WaveTurbulence.GammaLow.FinalCount.Count
