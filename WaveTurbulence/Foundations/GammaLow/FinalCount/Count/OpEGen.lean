/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEPiece
import Mathlib.Tactic

/-! # Operation (e) on a generalized theta chain (packet L6-COUNT, item D / Case6TopLow; M2 Lemma 4.3)

In case (6d) of Prop 9.6 (M2 §4.10) operation (e) removes `S = {p, q} ∪ C ∪ C'` where `p, q` are joined by three
connections: a bond `a`, a second connection `b` which is a bond or runs through a chain `C'`, and the chain `C` (entered
by `z₁` at `p`, `z₂` at `q`) whose total charge `w = k_{z₁} − k_{z₂}` is large. The case `C' = ∅` is M2 Lemma 4.3 after
operation (d) on `C`; `C' ≠ ∅` is the case where the double bond `p = q` of M2 contains an earlier operation-(d) bond
(on `C'`), counted here without performing that operation (d).

**The count** (`opE_gen_piece_count`): the unknowns are `k_a, k_b, k_{z₁}` (a decoration is determined by them:
`IsThetaGen.decoration_eq`, the chains by `chain_agree`); the conservation law at `p` (no three equal signs) gives two
free vectors `x, y` with `|x·y − α| ≤ τ` (Lemma 2.3(2) identity, `normTuple_inner`); the energy windows of the atoms of
`C` sum, by the boundary identity, to `−s(2w·k_{z₁} − |w|²)`, i.e. `|w·ξ − β'| ≤ |C|τ` with `ξ ∈ {y, x + y}`. Lemma
2.1(ii) (`coupledPair_vol_bound`, at `δ/3`) gives `≤ 9 C δ⁻¹ L^{2(d−γ)} min(1, τ/ρ)` for `|C| ≤ 3`, `|w| ≥ ρ`. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The generalized theta chain**: `M.atoms = {p, q} ∪ C ∪ C'` (disjoint), `p` has exactly the darts `a, b, z₁`, `q`
has degree three; `a` ends at `q`; `b` ends at `q` (then `C' = ∅`) or in `C'`; the chain `C` is attached exactly by
`mate z₁` and `mate z₂` (`z₂` at `q`), in one direction; all atoms of `C ∪ C'` have in = out = 1; `C`, `C'` connected; no
three equal signs at `p`; no loops. -/
structure IsThetaGen (M : Molecule V D) (p q : V) (a b z₁ z₂ : D) (C C' : Finset V) : Prop where
  hp : p ∈ M.atoms
  hq : q ∈ M.atoms
  hpq : p ≠ q
  hab : a ≠ b
  haz : a ≠ z₁
  hbz : b ≠ z₁
  starp : M.dartsAt p = {a, b, z₁}
  degq : M.deg q = 3
  atoms_eq : M.atoms \ {p, q} = C ∪ C'
  disj : Disjoint C C'
  hma : M.atom (M.mate a) = q
  hmb : (C' = ∅ ∧ M.atom (M.mate b) = q) ∨ M.atom (M.mate b) ∈ C'
  z₁in : M.atom (M.mate z₁) ∈ C
  hz₂ : M.atom z₂ = q
  z₂in : M.atom (M.mate z₂) ∈ C
  crossC : crossDarts M C = {M.mate z₁, M.mate z₂}
  signs : ¬ (M.out a = M.out b ∧ M.out b = M.out z₁)
  dir : M.out z₁ ≠ M.out z₂
  chain : ∀ v ∈ C ∪ C', M.outdeg v = 1 ∧ M.indeg v = 1
  connC : ∀ u ∈ C, ∀ v ∈ C, (piece M C).SameComponent u v
  connC' : ∀ u ∈ C', ∀ v ∈ C', (piece M C').SameComponent u v
  noLoop : ∀ x, M.atom x ≠ M.atom (M.mate x)

namespace IsThetaGen
variable {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} {C C' : Finset V} (h : IsThetaGen M p q a b z₁ z₂ C C')
include h

theorem atom_of_p {z : D} (hz : M.atom z = p) : z = a ∨ z = b ∨ z = z₁ := by
  have hm : z ∈ M.dartsAt p := (Mole.mem_dartsAt M p z).mpr hz
  rw [h.starp] at hm
  simpa using hm

theorem atom_a : M.atom a = p := (Mole.mem_dartsAt M p a).mp (by rw [h.starp]; simp)
theorem atom_b : M.atom b = p := (Mole.mem_dartsAt M p b).mp (by rw [h.starp]; simp)
theorem atom_z₁ : M.atom z₁ = p := (Mole.mem_dartsAt M p z₁).mp (by rw [h.starp]; simp)

theorem C_sub : C ⊆ M.atoms := fun v hv => (mem_sdiff.mp (h.atoms_eq ▸ mem_union_left _ hv)).1
theorem C'_sub : C' ⊆ M.atoms := fun v hv => (mem_sdiff.mp (h.atoms_eq ▸ mem_union_right _ hv)).1
theorem q_notC {v : V} (hv : v ∈ C ∪ C') : v ≠ q := by
  intro e; have := (mem_sdiff.mp (h.atoms_eq ▸ hv)).2; rw [e] at this; simp at this

theorem mz₁_ne_mz₂ : M.mate z₁ ≠ M.mate z₂ := by
  intro he
  have : z₁ = z₂ := by have := congrArg M.mate he; rwa [M.mate_mate, M.mate_mate] at this
  exact h.hpq (by rw [← h.atom_z₁, ← h.hz₂, this])

theorem dartSign_z₂ : M.dartSign z₂ = - M.dartSign z₁ := by
  unfold Molecule.dartSign
  have hd := h.dir
  cases h1 : M.out z₁ <;> cases h2 : M.out z₂ <;> simp_all

/-- **The chain charge** of `C`: `s₁ (k_{z₁} − k_{z₂}) = − ∑_{C} c_v`. -/
theorem chain_sum {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ) :
    M.dartSign z₁ • (Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂) = - ∑ v ∈ C, c v := by
  rw [sum_charges_eq_cross hκ h.C_sub, h.crossC, sum_pair h.mz₁_ne_mz₂, dartSign_mate, dartSign_mate, h.dartSign_z₂]
  simp only [Molecule.kvec, hκ.1]
  rw [smul_sub, neg_add, neg_smul, neg_smul, neg_neg, neg_smul]
  abel

/-- **The chain energy**: `∑_{v ∈ C} Γ_v = − s₁ (|k_{z₁}|² − |k_{z₂}|²)`. -/
theorem chain_gamma {d : ℕ} (L : ℝ) {κ : D → (Fin d → ℤ)} (hκ : ∀ x, κ (M.mate x) = κ x) :
    ∑ v ∈ C, M.Gamma L 0 κ v =
      - M.dartSign z₁ * (‖Molecule.kvec L 0 κ z₁‖ ^ 2 - ‖Molecule.kvec L 0 κ z₂‖ ^ 2) := by
  rw [sum_gamma_eq_cross M L 0 hκ C, h.crossC, sum_pair h.mz₁_ne_mz₂, dartSign_mate, dartSign_mate, h.dartSign_z₂]
  simp only [Molecule.kvec, hκ]
  ring

theorem chain_diff_eq {d : ℕ} {L : ℝ} {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ)
    (hκ' : M.IsDecoration L 0 c κ') :
    Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂ = Molecule.kvec L 0 κ' z₁ - Molecule.kvec L 0 κ' z₂ := by
  have e := (h.chain_sum hκ).trans (h.chain_sum hκ').symm
  have hs : M.dartSign z₁ ≠ 0 := by unfold Molecule.dartSign; split_ifs <;> norm_num
  exact smul_right_injective _ hs e

/-- **Determination**: a decoration is determined by its charges and its labels at `a, b, z₁`. -/
theorem decoration_eq {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) (hκ' : M.IsDecoration L 0 c κ') (ha : κ a = κ' a) (hb : κ b = κ' b)
    (hz : κ z₁ = κ' z₁) : κ = κ' := by
  have hagC := FinalCountG8.chain_agree M h.C_sub (fun v hv => h.chain v (mem_union_left _ hv)) h.connC hL hκ hκ'
    (z0 := M.mate z₁) h.z₁in (by rw [hκ.1, hκ'.1, hz])
  have hagC' : ∀ z, M.atom z ∈ C' → κ z = κ' z := by
    intro z hz'
    rcases h.hmb with ⟨hC', _⟩ | hbC'
    · rw [hC'] at hz'; simp at hz'
    · exact FinalCountG8.chain_agree M h.C'_sub (fun v hv => h.chain v (mem_union_right _ hv)) h.connC' hL hκ hκ'
        (z0 := M.mate b) hbC' (by rw [hκ.1, hκ'.1, hb]) z hz'
  have hag : ∀ z, M.atom z ∈ C ∪ C' → κ z = κ' z := fun z hz =>
    (mem_union.mp hz).elim (hagC z) (hagC' z)
  have hmem : ∀ z, M.atom z = p ∨ M.atom z = q ∨ M.atom z ∈ C ∪ C' := by
    intro z
    by_cases hzp : M.atom z = p
    · exact Or.inl hzp
    by_cases hzq : M.atom z = q
    · exact Or.inr (Or.inl hzq)
    exact Or.inr (Or.inr (h.atoms_eq ▸ mem_sdiff.mpr ⟨M.atom_mem z, by simp [hzp, hzq]⟩))
  funext z
  rcases hmem z with hzp | hzq | hzC
  · rcases h.atom_of_p hzp with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hz
  · rcases hmem (M.mate z) with hmp | hmq | hmC
    · rcases h.atom_of_p hmp with e | e | e
      · rw [← hκ.1, ← hκ'.1, e, ha]
      · rw [← hκ.1, ← hκ'.1, e, hb]
      · exfalso
        have := h.z₁in; rw [← e, M.mate_mate, hzq] at this
        exact h.q_notC (mem_union_left _ this) rfl
    · exact absurd (hzq.trans hmq.symm) (h.noLoop z)
    · rw [← hκ.1, ← hκ'.1]; exact hag _ hmC
  · exact hag z hzC

end IsThetaGen

/-- **The count of the generalized theta chain** (M2 Lemma 4.3, Lemma 2.1(ii)), `0 < γ ≤ 1/2`, `|C| ≤ 3`: if every
admissible decoration has `|k_{z₁} − k_{z₂}| ≥ ρ` (`0 < ρ ≤ 1`), then
`𝔈 ≤ 9 C δ⁻¹ L^{2(d−γ)} · min(1, δ⁻¹ L^{−2γ}/ρ)`. -/
theorem opE_gen_piece_count (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (p q : V) (a b z₁ z₂ : D)
      (K K' : Finset V), IsThetaGen M p q a b z₁ z₂ K K' → K.card ≤ 3 → ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖) →
      ∃ n : ℕ, (n : ℝ) ≤ C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) ∧
        MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤ n := by
  obtain ⟨C₀, L₀, hC₀, hvol⟩ := coupledPair_vol_bound d hd γ hγ
  refine ⟨9 * C₀, max L₀ 1, by positivity, ?_⟩
  intro L hL δ hδ ρ hρ hρ1 V D _ _ _ M p q a b z₁ z₂ K K' hT hK3 Adm hAdm
  classical
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  have hδ0 := hδ.1
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hδ3 : δ / 3 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith [hδ.2]⟩
  have hτ3 : (δ / 3)⁻¹ * L ^ (-2 * γ) = 3 * τ := by rw [hτ, inv_div, div_eq_mul_inv]; ring
  set B := 9 * C₀ * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (τ / ρ) with hBdef
  have hm0 : 0 ≤ min 1 (τ / ρ) := le_min zero_le_one (by positivity)
  have hB0 : 0 ≤ B := by positivity
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
  -- the bound of the coupled set at width `3τ`
  have hfinal : ∀ (ax ay : Mom d) (α β' : ℝ) (sel : Fin 3) (Rv : Mom d), ρ ≤ ‖Rv‖ →
      (coupledPairSet L ax ay Rv α β' ((δ / 3)⁻¹ * L ^ (-2 * γ)) sel).Finite ∧
      ((coupledPairSet L ax ay Rv α β' ((δ / 3)⁻¹ * L ^ (-2 * γ)) sel).ncard : ℝ) ≤ B := by
    intro ax ay α β' sel Rv hR
    obtain ⟨hf, hc⟩ := hvol L hLL (δ / 3) hδ3 ρ hρ hρ1 ax ay Rv hR α β' sel
    refine ⟨hf, hc.trans ?_⟩
    rw [hτ3]
    have hmin : min 1 (3 * τ / ρ) ≤ 3 * min 1 (τ / ρ) := by
      rcases le_total 1 (τ / ρ) with h1 | h1
      · rw [min_eq_left h1]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h1, mul_div_assoc]; exact min_le_right _ _
    have hδ' : (δ / 3)⁻¹ = 3 * δ⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [hδ', hBdef]
    have h0 : 0 ≤ C₀ * (3 * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by positivity
    calc C₀ * (3 * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * min 1 (3 * τ / ρ)
        ≤ C₀ * (3 * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * (3 * min 1 (τ / ρ)) := mul_le_mul_of_nonneg_left hmin h0
      _ = _ := by ring
  -- the fixed chain difference
  set Rv : Mom d := Molecule.kvec L 0 κ0 z₁ - Molecule.kvec L 0 κ0 z₂ with hRv
  have hR : ∀ κ ∈ A, latticePoint L (κ z₂) = latticePoint L (κ z₁) - Rv := by
    intro κ hκ
    have e := hT.chain_diff_eq hκ.1 hκ0.1
    simp only [Molecule.kvec, zero_add] at e hRv
    rw [hRv, ← e]; abel
  have hRρ : ρ ≤ ‖Rv‖ := hAdm κ0 hκ0.2.2
  -- the energy window on `R · k_{z₁}` from the windows of `C`
  set s₁ := M.dartSign z₁ with hs₁
  have hs1sq : s₁ * s₁ = 1 := by rw [hs₁]; unfold Molecule.dartSign; split_ifs <;> norm_num
  have hs1abs : |s₁| = 1 := by rw [hs₁]; unfold Molecule.dartSign; split_ifs <;> norm_num
  set βs : ℝ := (‖Rv‖ ^ 2 - s₁ * ∑ v ∈ K, β v) / 2 with hβs
  have hER : ∀ κ ∈ A, |inner ℝ Rv (latticePoint L (κ z₁)) - βs| ≤ 3 * τ := by
    intro κ hκ
    have hG := hT.chain_gamma L hκ.1.1
    simp only [Molecule.kvec, zero_add] at hG
    rw [hR κ hκ] at hG
    set k := latticePoint L (κ z₁)
    have hwin : |∑ v ∈ K, M.Gamma L 0 κ v - ∑ v ∈ K, β v| ≤ 3 * τ := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ v ∈ K, |M.Gamma L 0 κ v - β v| ≤ ∑ _v ∈ K, τ := sum_le_sum fun v hv => hκ.2.1.1 v (hT.C_sub hv)
        _ = K.card * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 3 * τ := mul_le_mul_of_nonneg_right (by exact_mod_cast hK3) hτ0.le
    rw [hG] at hwin
    have hsq : ‖k - Rv‖ ^ 2 = ‖k‖ ^ 2 - 2 * inner ℝ k Rv + ‖Rv‖ ^ 2 := norm_sub_sq_real k Rv
    have e2 : 2 * (inner ℝ Rv k - βs) =
        -s₁ * (-s₁ * (‖k‖ ^ 2 - ‖k - Rv‖ ^ 2) - ∑ v ∈ K, β v) := by
      rw [hβs, hsq, real_inner_comm Rv k]; linear_combination (-(2 * inner ℝ Rv k - ‖Rv‖ ^ 2)) * hs1sq
    have h2 : |2 * (inner ℝ Rv k - βs)| ≤ 3 * τ := by
      rw [e2, abs_mul, abs_neg, hs1abs, one_mul]; exact hwin
    rw [abs_mul, abs_two] at h2
    have : |inner ℝ Rv k - βs| ≤ 3 * τ / 2 := by linarith
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
  have h3τ : 3 * τ = (δ / 3)⁻¹ * L ^ (-2 * γ) := hτ3.symm
  have hz1 : ∀ κ ∈ A, |inner ℝ Rv (latticePoint L (κ z₁ - m)) - β₀| ≤ (δ / 3)⁻¹ * L ^ (-2 * γ) := by
    intro κ hκ
    rw [hinner κ hκ, hβ₀, show inner ℝ Rv (latticePoint L (κ z₁)) - inner ℝ Rv (latticePoint L m) -
      (βs - inner ℝ Rv (latticePoint L m)) = inner ℝ Rv (latticePoint L (κ z₁)) - βs by ring, ← h3τ]
    exact hER κ hκ
  have hwid : ∀ {x : ℝ}, x ≤ τ → x ≤ (δ / 3)⁻¹ * L ^ (-2 * γ) := fun hx => by rw [← h3τ]; linarith
  -- the three normalized shapes
  rcases hsh with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 1 2 0 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hfinal (k0 b - latticePoint L m) (k0 z₁ - latticePoint L m) α₀ β₀ 1 Rv hRρ
    have hmem : ∀ κ ∈ A, (κ b - m, κ z₁ - m) ∈
        coupledPairSet L (k0 b - latticePoint L m) (k0 z₁ - latticePoint L m) Rv α₀ β₀
          ((δ / 3)⁻¹ * L ^ (-2 * γ)) 1 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf1, hnf2] at hi
      exact ⟨nearLattice_sub m (hnear κ hκ b), nearLattice_sub m (hnear κ hκ z₁), hwid hi, hz1 κ hκ⟩
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
  · have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 0 2 1 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hfinal (k0 a - latticePoint L m) (k0 z₁ - latticePoint L m) α₀ β₀ 1 Rv hRρ
    have hmem : ∀ κ ∈ A, (κ a - m, κ z₁ - m) ∈
        coupledPairSet L (k0 a - latticePoint L m) (k0 z₁ - latticePoint L m) Rv α₀ β₀
          ((δ / 3)⁻¹ * L ^ (-2 * γ)) 1 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf0, hnf2] at hi
      exact ⟨nearLattice_sub m (hnear κ hκ a), nearLattice_sub m (hnear κ hκ z₁), hwid hi, hz1 κ hκ⟩
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
  · have hN' : ∀ κ ∈ A, NormTuple L (nf κ) 0 1 2 m (s * β p) τ := fun κ hκ => hN κ hκ
    obtain ⟨hfin, hcnt⟩ := hfinal (k0 a - latticePoint L m) (k0 b - latticePoint L m) α₀ β₀ 2 Rv hRρ
    have hez : ∀ κ ∈ A, κ z₁ = κ a + κ b - m := by
      intro κ hκ
      have e1 := (hN' κ hκ).1
      rw [hnf0, hnf1, hnf2] at e1
      rw [← e1]; abel
    have hmem : ∀ κ ∈ A, (κ a - m, κ b - m) ∈
        coupledPairSet L (k0 a - latticePoint L m) (k0 b - latticePoint L m) Rv α₀ β₀
          ((δ / 3)⁻¹ * L ^ (-2 * γ)) 2 := by
      intro κ hκ
      have hi := normTuple_inner (hN' κ hκ)
      rw [hnf0, hnf1] at hi
      have h4 : |inner ℝ Rv (latticePoint L (κ a - m) + latticePoint L (κ b - m)) - β₀| ≤
          (δ / 3)⁻¹ * L ^ (-2 * γ) := by
        rw [← WeylSums.latticePoint_add_eq, show κ a - m + (κ b - m) = κ z₁ - m by rw [hez κ hκ]; abel]
        exact hz1 κ hκ
      exact ⟨nearLattice_sub m (hnear κ hκ a), nearLattice_sub m (hnear κ hκ b), hwid hi, h4⟩
    have hinj : Set.InjOn (fun κ : D → (Fin d → ℤ) => (κ a - m, κ b - m)) A := by
      intro κ hκ κ' hκ' he
      simp only [Prod.mk.injEq, sub_left_inj] at he
      have h2 : κ z₁ = κ' z₁ := by rw [hez κ hκ, hez κ' hκ', he.1, he.2]
      exact hT.decoration_eq hLp.ne' hκ.1 hκ'.1 he.1 he.2 h2
    exact (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn _ hmem hinj hfin)).trans hcnt

end
end WaveTurbulence.GammaLow.FinalCount.Count
