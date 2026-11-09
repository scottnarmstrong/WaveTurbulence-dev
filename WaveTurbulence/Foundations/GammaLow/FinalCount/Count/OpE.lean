/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEPiece
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.TwoExitOff
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExitBound
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNormAdm
import Mathlib.Tactic

/-! # Operation (d)+(e) at `0 < γ ≤ 1/2`: `opE_bound` (packet L6-COUNT, item D; M2 Lemma 4.3)

DH23 (opere) L1869–L1871, read at `γ ≤ 1/2` as M2 Lemma 4.3 (with the uncapped A.2(1), F-M2-2): removing the theta chain
`S = C ∪ {p, q}` (`IsThetaChain` on the piece `𝕄[S]`) costs
`𝔇_{de} ≤ C (log L)^B min(1, δ⁻¹ L^{−2γ}/ρ)`, `ρ ≤ |k_{z₁} − k_{z₂}|` (the total charge `w` of the chain `C`, M2's `P`).
`Δχ = −2` in all three external configurations of M2 Lemma 4.3 (REF-M2 §2.4):
* `opE_none`: no external bond (`S` is the whole molecule, `ΔF = −1`);
* `opE_one`: one external bond (`OneExit`: its value is fixed by conservation over `S`; post `𝕄 ∖ S`);
* `opE_bound` (the main configuration): two externals at `p` and `q` (`TwoExit`: `S` attached by two bonds of opposite directions; post
  `𝕄 ∖ S` plus the bond `s – t`, labels `k_{ℓ_q} + g(k_{ℓ_p} − k_{ℓ_q})`, `g ∈ {0,…,4}`, LG off `Bs` weakened to `η/2`,
  exactly as main's operation (d) `OpDW`).
With `ρ ≥ L^{−γ−100η}/2` the deviation is `≲ (log L)^B δ⁻¹ L^{−γ+100η}` (`opE_min_le`; M2: (opere) with `100η` for
`200η`).

Shared lemmas: `IsThetaChain.circuitRank_eq` (a connected theta chain has `χ = 2`), `cellProduct_le_pow` (cells of a
molecule with at most five atoms), `norm_split_le` (normalization across a removal with `χ(N) ≥ χ(S) + χ(post)`). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **A connected theta chain has circuit rank two** (`|C| + 3` bonds on `|C| + 2` atoms). -/
theorem IsThetaChain.circuitRank_eq {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} (h : IsThetaChain M p q a b z₁ z₂)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) : M.circuitRank = 2 := by
  classical
  have hF : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨p, h.hp⟩ hconn
  have hsum := Mole.sum_degrees_eq_two_mul_bonds M
  have hdp : M.deg p = 3 := by
    unfold Molecule.deg; rw [h.starp]
    rw [card_insert_of_notMem (by simp [h.hab, h.haz]), card_pair h.hbz]
  have hdq : M.deg q = 3 := by
    unfold Molecule.deg; rw [h.starq]
    rw [card_insert_of_notMem (by simp [h.hmab, h.hmaz]), card_pair h.hmbz]
  have hpq : ({p, q} : Finset V) ⊆ M.atoms := by
    intro x hx; rcases mem_insert.mp hx with rfl | hx
    · exact h.hp
    · rw [mem_singleton.mp hx]; exact h.hq
  have hs := sum_sdiff hpq (f := M.deg)
  rw [sum_pair h.hpq, hdp, hdq] at hs
  have hC : ∑ v ∈ M.atoms \ {p, q}, M.deg v = ∑ _v ∈ M.atoms \ {p, q}, 2 := by
    refine sum_congr rfl fun v hv => ?_
    rw [← Mole.outdeg_add_indeg M v, (h.chain v hv).1, (h.chain v hv).2]
  rw [hC, sum_const, smul_eq_mul] at hs
  have hcard := card_sdiff_of_subset hpq
  rw [card_pair h.hpq] at hcard
  have hc2 : 2 ≤ M.atoms.card := by have := card_le_card hpq; rwa [card_pair h.hpq] at this
  unfold Molecule.circuitRank
  rw [hF]
  omega

/-- **Cells of a small molecule**: `𝔠(𝕄) ≤ ((log L)²)^{2^{|𝕄|}}`. -/
theorem cellProduct_le_pow (M : Molecule V D) {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hlog : 1 ≤ Real.log L)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) :
    MoleProp.cellProduct M L γ δ P ≤ (Real.log L ^ 2) ^ (2 ^ M.atoms.card) := by
  classical
  have hlog2 : 1 ≤ Real.log L ^ 2 := by nlinarith
  unfold MoleProp.cellProduct
  calc ∏ S ∈ MoleProp.ladderCells M, Molecule.ladderWeight L γ δ (P S)
      ≤ ∏ _S ∈ MoleProp.ladderCells M, Real.log L ^ 2 :=
        Finset.prod_le_prod₀ (fun S hS => ladderWeight_nonneg hL hδ (hP S hS)) (fun S _ => ladderWeight_le_log_sq L γ δ _)
    _ = (Real.log L ^ 2) ^ (MoleProp.ladderCells M).card := Finset.prod_const _
    _ ≤ (Real.log L ^ 2) ^ (2 ^ M.atoms.card) := by
        refine pow_le_pow_right₀ hlog2 ?_
        calc (MoleProp.ladderCells M).card ≤ M.atoms.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 ^ M.atoms.card := Finset.card_powerset _

end

/-- **The normalization across a removal**: `χ_S + χ_post ≤ χ_N`, `b ≤ 1`, `c_N ≤ c_S c_post` give
`L^{−aχ_N} b^{χ_N} c_N ≤ (L^{−aχ_S} b^{χ_S} c_S)(L^{−aχ_post} b^{χ_post} c_post)`. -/
theorem norm_split_le {L a b cN cp cq : ℝ} {χN χp χq : ℤ} (hL : 1 ≤ L) (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1)
    (he : χp + χq ≤ χN) (hcp : 0 ≤ cp) (hcq : 0 ≤ cq) (hcN : cN ≤ cp * cq) :
    L ^ (-a * χN) * b ^ χN * cN ≤ (L ^ (-a * χp) * b ^ χp * cp) * (L ^ (-a * χq) * b ^ χq * cq) := by
  have hLp : 0 < L := by linarith
  set e := χN - χp - χq with hedef
  have he0 : 0 ≤ e := by omega
  have hχ : χN = χp + χq + e := by omega
  have hLpow : L ^ (-a * χN) = L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) := by
    rw [← Real.rpow_add hLp, ← Real.rpow_add hLp, hχ]; push_cast; ring_nf
  have hLe : L ^ (-a * e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by
    have : (0 : ℝ) ≤ e := by exact_mod_cast he0
    nlinarith)
  have hbpow : b ^ χN = b ^ χp * b ^ χq * b ^ e := by
    rw [hχ, zpow_add₀ hb.ne', zpow_add₀ hb.ne']
  have hbe : b ^ e ≤ 1 := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le he0
    rw [hn, zpow_natCast]; exact pow_le_one₀ hb.le hb1
  have h1 : 0 ≤ L ^ (-a * χp) := (Real.rpow_pos_of_pos hLp _).le
  have h2 : 0 ≤ L ^ (-a * χq) := (Real.rpow_pos_of_pos hLp _).le
  have h3 : 0 ≤ L ^ (-a * e) := (Real.rpow_pos_of_pos hLp _).le
  have h4 : 0 ≤ b ^ χp := (zpow_pos hb _).le
  have h5 : 0 ≤ b ^ χq := (zpow_pos hb _).le
  have h6 : 0 ≤ b ^ e := (zpow_pos hb _).le
  rw [hLpow, hbpow]
  rcases le_or_gt 0 cN with h0 | h0
  · calc L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) * (b ^ χp * b ^ χq * b ^ e) * cN
        ≤ L ^ (-a * χp) * L ^ (-a * χq) * 1 * (b ^ χp * b ^ χq * 1) * (cp * cq) := by gcongr
      _ = _ := by ring
  · have : L ^ (-a * χp) * L ^ (-a * χq) * L ^ (-a * e) * (b ^ χp * b ^ χq * b ^ e) * cN ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
    exact this.trans (by positivity)

/-- The constant bookkeeping of a theta-chain removal: `n · L^{−2(d−γ)} (C₁⁻¹δ^{1/2})² 𝔠_S ≤ C (log L)^{64} m`. -/
theorem opE_const {d : ℕ} {L γ δ C C1 m cS : ℝ} {n : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC1 : 1 ≤ C1) (hm : 0 ≤ m)
    (hC : 0 ≤ C) (hn : (n : ℝ) ≤ C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * m) (hcS0 : 0 ≤ cS)
    (hcS : cS ≤ (Real.log L ^ 2) ^ 32) :
    (n : ℝ) * (L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) * cS) ≤
      C * Real.log L ^ (64 : ℕ) * m := by
  have hLp : 0 < L := by linarith
  have hC1p : 0 < C1 := by linarith
  have hsq : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) = C1⁻¹ ^ 2 * δ := by
    rw [zpow_ofNat, mul_pow, ← Real.rpow_natCast (δ ^ (1 / 2 : ℝ)), ← Real.rpow_mul hδ.le]
    norm_num
  have hLL : L ^ (2 * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) = 1 := by
    rw [← Real.rpow_add hLp]; norm_num; ring_nf; exact Real.rpow_zero L
  have hC1i : C1⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hC1)
  have hlog : (Real.log L ^ 2) ^ 32 = Real.log L ^ (64 : ℕ) := by rw [← pow_mul]
  have hA : 0 ≤ L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) * cS := by
    rw [hsq]; have := Real.rpow_pos_of_pos hLp (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)); positivity
  calc (n : ℝ) * (L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) * cS)
      ≤ (C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) * m) *
          (L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) * cS) :=
        mul_le_mul_of_nonneg_right hn hA
    _ = C * m * (C1⁻¹ ^ 2 * cS) * (δ⁻¹ * δ) *
          (L ^ (2 * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ))) := by rw [hsq]; ring
    _ = C * m * (C1⁻¹ ^ 2 * cS) := by rw [hLL, inv_mul_cancel₀ hδ.ne']; ring
    _ ≤ C * m * (1 * (Real.log L ^ 2) ^ 32) := by
        gcongr
    _ = C * Real.log L ^ (64 : ℕ) * m := by rw [hlog]; ring

/-- **Operation (d)+(e), no external bond** (M2 Lemma 4.3, `ΔF = −1`): the whole molecule is a connected theta chain
with at most five atoms; then `𝔄(𝕄) ≤ C (log L)^{64} min(1, δ⁻¹L^{−2γ}/ρ)`. -/
theorem opE_none (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 ≥ (1 : ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (p q : V) (a b z₁ z₂ : D),
      IsThetaChain M p q a b z₁ z₂ → M.atoms.card ≤ 5 →
      (∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (C * Real.log L ^ (64 : ℕ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ)) := by
  obtain ⟨C, L₀, hC, hcnt⟩ := opE_piece_count d hd γ hγ
  refine ⟨C, max L₀ (Real.exp 1), hC.le, ?_⟩
  intro L hL δ hδ C1 hC1 ρ hρ hρ1 V D _ _ _ M p q a b z₁ z₂ hT hM5 hconn P hP Adm hAdm
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  obtain ⟨n, hn, hE⟩ := hcnt L ((le_max_left _ _).trans hL) δ hδ ρ hρ hρ1 M p q a b z₁ z₂ hT Adm hAdm
  have hm : 0 ≤ min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := le_min zero_le_one (by have := hδ.1; positivity)
  have hcS0 : 0 ≤ MoleProp.cellProduct M L γ δ P :=
    (MoleProp.cellProduct_pos M hLp.le hδ.1.le (by positivity) P hP).le
  have hcS : MoleProp.cellProduct M L γ δ P ≤ (Real.log L ^ 2) ^ 32 := by
    refine (cellProduct_le_pow M hLp.le hδ.1.le hlog P hP).trans (pow_le_pow_right₀ (by nlinarith) ?_)
    calc 2 ^ M.atoms.card ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hM5
      _ = 32 := by norm_num
  have hE' : (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    have := ENat.toENNReal_mono hE; simpa using this
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P) := mul_le_mul' hE' le_rfl
    _ = ENNReal.ofReal ((n : ℝ) * MoleProp.freeNormalization M (d := d) L γ δ C1 P) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold MoleProp.freeNormalization
        rw [hT.circuitRank_eq hconn]
        exact opE_const hL1 hδ.1 hC1 hm hC.le hn hcS0 hcS

/-- **Operation (d)+(e), one external bond** (M2 Lemma 4.3; `OneExit`): `S` (at most five atoms) is attached by one
bond, its piece is a connected theta chain; then `𝔄(𝕄) ≤ C (log L)^{64} min(1, δ⁻¹L^{−2γ}/ρ) · 𝔄(𝕄 ∖ S)`. -/
theorem opE_one (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 ≥ (1 : ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D) (T : OneExit N),
      T.Y.card ≤ 5 → ∀ (p q : V) (a b z₁ z₂ : Degen.RetainedDart N (N.atoms \ T.Y)),
      IsThetaChain (piece N T.Y) p q a b z₁ z₂ → (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁.val - Molecule.kvec L 0 κ z₂.val‖) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (C * Real.log L ^ (64 : ℕ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ)) *
            MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
              (MoleProp.erasedFreeAdmissibility N T.Y Adm) P := by
  obtain ⟨C, L₀, hC, hcnt⟩ := opE_piece_count d hd γ hγ
  refine ⟨C, max L₀ (Real.exp 1), hC.le, ?_⟩
  intro L hL δ hδ C1 hC1 ρ hρ hρ1 V D _ _ _ N T hY5 p q a b z₁ z₂ hT hconnP P hP Adm hAdm
  classical
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have hδ0 := hδ.1
  obtain ⟨n, hn, hE⟩ := hcnt L ((le_max_left _ _).trans hL) δ hδ ρ hρ hρ1 (piece N T.Y) p q a b z₁ z₂ hT
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) (by
      rintro κ' ⟨κ, hA, -, rfl⟩; exact hAdm κ hA)
  have hm : 0 ≤ min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := le_min zero_le_one (by positivity)
  -- cells
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms N T.Y), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff N T.Y S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩)
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  have hcS0 : 0 ≤ MoleProp.cellProduct (piece N T.Y) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ0.le hlog0 P hPpiece).le
  have hcE0 : 0 ≤ MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ0.le hlog0 P hPerase).le
  have hcS : MoleProp.cellProduct (piece N T.Y) L γ δ P ≤ (Real.log L ^ 2) ^ 32 := by
    refine (cellProduct_le_pow _ hLp.le hδ0.le hlog P hPpiece).trans (pow_le_pow_right₀ (by nlinarith) ?_)
    rw [piece_atoms T.sub]
    calc 2 ^ T.Y.card ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hY5
      _ = 32 := by norm_num
  have hcells : MoleProp.cellProduct N L γ δ P =
      MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P := by
    have := congrArg (fun f => f L γ δ P) T.ladderCells_eq_union
    simpa using this
  -- ranks
  have hconnP' : ∀ u ∈ (piece N T.Y).atoms, ∀ v ∈ (piece N T.Y).atoms, (piece N T.Y).SameComponent u v := by
    rw [piece_atoms T.sub]; exact hconnP
  have hrkP := hT.circuitRank_eq hconnP'
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one _ ⟨p, hT.hp⟩ hconnP'
  have hid := T.circuitRank_identity
  have hFle := T.erase_numComponents_le
  have hrk : (piece N T.Y).circuitRank + (Degen.eraseAtoms N T.Y).circuitRank ≤ N.circuitRank := by
    rw [hFp] at hid; omega
  -- normalizations
  have hb : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by have : 0 < C1 := by linarith
                                             positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ0.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have ha : (0 : ℝ) ≤ (d : ℝ) - γ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [hγ.2]
  have hnorm := norm_split_le (a := (d : ℝ) - γ) hL1 ha hb hb1 hrk hcS0 hcE0 hcells.le
  rw [hrkP] at hnorm
  set X := L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) *
    MoleProp.cellProduct (piece N T.Y) L γ δ P with hX
  have hX0 : 0 ≤ X := by rw [hX]; have := Real.rpow_pos_of_pos hLp (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)); positivity
  have hconst := opE_const (d := d) hL1 hδ0 hC1 hm hC.le hn hcS0 hcS
  -- counts
  have h1 : (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤
      (n : ℝ≥0∞) * (MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility N T.Y Adm) : ℝ≥0∞) := by
    have := ENat.toENNReal_mono ((T.countEFree_le hLp Adm).trans (mul_le_mul' hE le_rfl))
    rw [ENat.toENNReal_mul] at this; simpa using this
  rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((n : ℝ≥0∞) * (MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y Adm) : ℝ≥0∞)) *
          ENNReal.ofReal (X * MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P) :=
        mul_le_mul' h1 (ENNReal.ofReal_le_ofReal (by unfold MoleProp.freeNormalization; exact hnorm))
    _ = ENNReal.ofReal ((n : ℝ) * X) * ((MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y Adm) : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P)) := by
        rw [ENNReal.ofReal_mul hX0, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl

/-- **Operation (d)+(e), two external bonds** (M2 Lemma 4.3; `TwoExit`, as main's operation (d) `OpDW`): `S` (at
most five atoms) is attached by the two bonds `x` (out, to `c`) and `y` (in, from `d ≠ c`), its piece is a connected
theta chain, LG holds off `Bs` and `W` selects good multipliers; then
`𝔄(𝕄) ≤ C (log L)^{78} min(1, δ⁻¹L^{−2γ}/ρ) · sup_{g, P'} 𝔄(post; postAdmOff)`. -/
theorem opE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 ≥ (1 : ℝ), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D) (T : TwoExit N),
      (∀ z, N.atom z ≠ N.atom (N.mate z)) → (∀ a ∈ N.atoms, N.deg a ≤ 4) →
      T.Y.card ≤ 5 → ∀ (p q : V) (a b z₁ z₂ : Degen.RetainedDart N (N.atoms \ T.Y)),
      IsThetaChain (piece N T.Y) p q a b z₁ z₂ → (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      ∀ (Bs : Finset V), (∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) →
      ∀ (η : ℝ) (P : Finset V → ℝ), (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff N Bs L γ η P κ) →
      (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁.val - Molecule.kvec L 0 κ z₂.val‖) →
      ∀ W : ℤ → (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) → ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g ∧ W g κ) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (C * Real.log L ^ (78 : ℕ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ)) *
            ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
              MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) P' := by
  obtain ⟨C, L₀, hC, hcnt⟩ := opE_piece_count d hd γ hγ
  refine ⟨55125 * C, max L₀ (Real.exp 1), by positivity, ?_⟩
  intro L hL δ hδ C1 hC1 ρ hρ hρ1 V D _ _ _ N T hloop hdeg hY5 p q a b z₁ z₂ hT hconnP Bs hopen η P hP Adm hAdm
    hgap W hW
  classical
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have hδ0 := hδ.1
  obtain ⟨n, hn, hE⟩ := hcnt L ((le_max_left _ _).trans hL) δ hδ ρ hρ hρ1 (piece N T.Y) p q a b z₁ z₂ hT
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) (by
      rintro κ' ⟨κ, hA, -, rfl⟩; exact hgap κ hA)
  have hm : 0 ≤ min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := le_min zero_le_one (by positivity)
  set fam := T.scaleFamily L P
  set Mn : ℕ := 5 * T.windowK ^ 2 * fam.card
  have hcount := twoExit_countEFree_le_off T hloop hdeg hopen (d := d) hL1 hδ0 P (γ := γ) (η := η) Adm Bs hAdm W hW
  -- the supremum over the finite family is attained
  set idx2 := Icc (0 : ℤ) 4 ×ˢ fam
  set G := fun pr : ℤ × (Finset V → ℝ) =>
    MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) pr.2 pr.1) with hG
  have hsupeq : (⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ fam,
      MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g)) = idx2.sup G := by
    rw [Finset.sup_eq_iSup]
    refine le_antisymm (iSup₂_le fun g hg => iSup₂_le fun P' hP' => ?_) (iSup₂_le fun pr hpr => ?_)
    · exact le_iSup₂_of_le (f := fun pr (_ : pr ∈ idx2) => G pr) (g, P') (mem_product.mpr ⟨hg, hP'⟩) le_rfl
    · obtain ⟨hg, hP'⟩ := mem_product.mp hpr
      refine le_iSup₂_of_le (f := fun g (_ : g ∈ Icc (0 : ℤ) 4) => ⨆ P' ∈ fam,
        MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g)) pr.1 hg ?_
      exact le_iSup₂_of_le (f := fun P' (_ : P' ∈ fam) => MoleProp.countEFree T.post L γ δ (0 : Mom d)
        (T.postAdmOff Bs Adm W L γ (η / 2) P' pr.1)) pr.2 hP' le_rfl
  rw [hsupeq] at hcount
  rcases idx2.eq_empty_or_nonempty with hfe | hfne
  · rw [hfe, Finset.sup_empty, bot_eq_zero, mul_zero] at hcount
    rw [MoleProp.countAFree_eq_normalization, nonpos_iff_eq_zero.mp hcount]
    simp
  obtain ⟨⟨g0, P0⟩, hgP0, hmax⟩ := exists_mem_eq_sup idx2 hfne G
  obtain ⟨hg0, hP0⟩ := mem_product.mp hgP0
  rw [hmax] at hcount
  -- cells
  have hP0nn := T.scaleFamily_nonneg hP0 (fun S hS hc => hP S (by
    have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N hcell.1), hcell.1⟩))
  have hagree := T.scaleFamily_agree hP0
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := by
    intro S hS; rw [T.ladderCells_piece_eq] at hS; exact hP S (mem_filter.mp hS).1
  have hcS0 : 0 ≤ MoleProp.cellProduct (piece N T.Y) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ0.le hlog0 P hPpiece).le
  have hcQ0 : 0 ≤ MoleProp.cellProduct T.post L γ δ P0 :=
    (MoleProp.cellProduct_pos _ hLp.le hδ0.le hlog0 P0 hP0nn).le
  have hcS : MoleProp.cellProduct (piece N T.Y) L γ δ P ≤ (Real.log L ^ 2) ^ 32 := by
    refine (cellProduct_le_pow _ hLp.le hδ0.le hlog P hPpiece).trans (pow_le_pow_right₀ (by nlinarith) ?_)
    rw [piece_atoms T.sub]
    calc 2 ^ T.Y.card ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hY5
      _ = 32 := by norm_num
  have hcells := T.cellProduct_le (γ := γ) hloop hdeg hLp.le hδ0.le hlog P P0 hP hP0nn hagree
  -- ranks
  have hconnP' : ∀ u ∈ (piece N T.Y).atoms, ∀ v ∈ (piece N T.Y).atoms, (piece N T.Y).SameComponent u v := by
    rw [piece_atoms T.sub]; exact hconnP
  have hrkP := hT.circuitRank_eq hconnP'
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one _ ⟨p, hT.hp⟩ hconnP'
  have hid := T.circuitRank_identity
  have hFle := T.post_numComponents_le
  have hrk : (piece N T.Y).circuitRank + T.post.circuitRank ≤ N.circuitRank := by
    rw [hFp] at hid; omega
  -- normalizations
  have hb : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by have : 0 < C1 := by linarith
                                             positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ0.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have ha : (0 : ℝ) ≤ (d : ℝ) - γ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [hγ.2]
  set Λ : ℝ := (Real.log L ^ 2) ^ 6 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hnorm := norm_split_le (a := (d : ℝ) - γ) (cN := MoleProp.cellProduct N L γ δ P)
    (cq := MoleProp.cellProduct T.post L γ δ P0 * Λ) hL1 ha hb hb1 hrk
    hcS0 (mul_nonneg hcQ0 hΛ0) (hcells.trans_eq (mul_assoc _ _ _))
  rw [hrkP] at hnorm
  set X := L ^ (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (2 : ℤ) *
    MoleProp.cellProduct (piece N T.Y) L γ δ P with hX
  have hX0 : 0 ≤ X := by rw [hX]; have := Real.rpow_pos_of_pos hLp (-((d : ℝ) - γ) * ((2 : ℤ) : ℝ)); positivity
  have hconst := opE_const (d := d) hL1 hδ0 hC1 hm hC.le hn hcS0 hcS
  have hnormQ : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      X * (MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 * Λ) := by
    unfold MoleProp.freeNormalization
    calc _ ≤ _ := hnorm
      _ = _ := by rw [hX]; ring
  -- the constant
  have hMn : (Mn : ℝ) ≤ 2205 * (25 * Real.log L ^ 2) := by
    have hfam : (fam.card : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := by
      exact_mod_cast T.card_scaleFamily_le hloop hdeg L P
    have hs := card_scaleSet_le_log hlog
    have hfam' : (fam.card : ℝ) ≤ 25 * Real.log L ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (scaleSet L).card]
    have hW : (T.windowK : ℝ) ≤ 21 := by
      have : T.windowK = 1 + 4 * T.Y.card := rfl
      rw [this]; push_cast
      have : (T.Y.card : ℝ) ≤ 5 := by exact_mod_cast hY5
      linarith
    have hW0 : (0 : ℝ) ≤ T.windowK := Nat.cast_nonneg _
    simp only [Mn]; push_cast
    calc 5 * (T.windowK : ℝ) ^ 2 * fam.card ≤ 5 * 21 ^ 2 * (25 * Real.log L ^ 2) := by gcongr
      _ = _ := by ring
  have hfinal : (Mn : ℝ) * ((n : ℝ) * X) * Λ ≤ 55125 * C * Real.log L ^ (78 : ℕ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := by
    have hnX0 : 0 ≤ (n : ℝ) * X := mul_nonneg (Nat.cast_nonneg _) hX0
    have hl : Real.log L ^ 2 * Real.log L ^ (64 : ℕ) * Λ = Real.log L ^ (78 : ℕ) := by rw [hΛ]; ring
    calc (Mn : ℝ) * ((n : ℝ) * X) * Λ ≤ (2205 * (25 * Real.log L ^ 2)) * (C * Real.log L ^ (64 : ℕ) *
          min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ)) * Λ := by gcongr
      _ = 55125 * C * (Real.log L ^ 2 * Real.log L ^ (64 : ℕ) * Λ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := by ring
      _ = _ := by rw [hl]
  -- assemble
  have h1 : (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤ (Mn : ℝ≥0∞) * (n : ℝ≥0∞) * (G (g0, P0) : ℝ≥0∞) := by
    have hc' : MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤ (Mn : ℕ∞) * (n : ℕ∞) * G (g0, P0) := by
      refine hcount.trans ?_
      simp only [Mn, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      exact mul_le_mul' (mul_le_mul' le_rfl hE) le_rfl
    have := ENat.toENNReal_mono hc'
    rw [ENat.toENNReal_mul, ENat.toENNReal_mul] at this
    simpa using this
  have hsup : MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P0 g0) P0 ≤
      ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
        MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) P' := by
    refine le_iSup₂_of_le (f := fun g (_ : g ∈ Icc (0 : ℤ) 4) => ⨆ P' ∈ fam,
      MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) P') g0 hg0 ?_
    exact le_iSup₂_of_le (f := fun P' (_ : P' ∈ fam) => MoleProp.countAFree T.post L γ δ C1 (0 : Mom d)
      (T.postAdmOff Bs Adm W L γ (η / 2) P' g0) P') P0 hP0 le_rfl
  have hnQ0 : 0 ≤ MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 :=
    (MoleProp.freeNormalization_pos T.post (d := d) (γ := γ) hLp hδ0 (by linarith) hlog0 P0 hP0nn).le
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((Mn : ℝ≥0∞) * (n : ℝ≥0∞) * (G (g0, P0) : ℝ≥0∞)) *
          ENNReal.ofReal (X * (MoleProp.freeNormalization T.post (d := d) L γ δ C1 P0 * Λ)) :=
        mul_le_mul' h1 (ENNReal.ofReal_le_ofReal hnormQ)
    _ = ENNReal.ofReal ((Mn : ℝ) * ((n : ℝ) * X) * Λ) *
          MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P0 g0) P0 := by
        rw [MoleProp.countAFree_eq_normalization, ENNReal.ofReal_mul hX0, ENNReal.ofReal_mul hnQ0,
          ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hX0)),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        simp only [hG]
        ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hfinal) hsup

/-- **The (6d) form of the deviation** (M2 §4.10, Lemma 4.3): if the chain charge satisfies `ρ ≥ L^{−γ−100η}/2`, then
`min(1, δ⁻¹L^{−2γ}/ρ) ≤ 2 δ⁻¹ L^{−γ+100η}`. -/
theorem opE_min_le {L γ η δ ρ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hρ : L ^ (-γ - 100 * η) / 2 ≤ ρ) :
    min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) ≤ 2 * δ⁻¹ * L ^ (-γ + 100 * η) := by
  have h0 : 0 < L ^ (-γ - 100 * η) := Real.rpow_pos_of_pos hL _
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ hρ0]
  have e : L ^ (-γ + 100 * η) * L ^ (-γ - 100 * η) = L ^ (-2 * γ) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  have hi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  calc δ⁻¹ * L ^ (-2 * γ) = 2 * δ⁻¹ * L ^ (-γ + 100 * η) * (L ^ (-γ - 100 * η) / 2) := by rw [← e]; ring
    _ ≤ 2 * δ⁻¹ * L ^ (-γ + 100 * η) * ρ := by
        have : 0 ≤ 2 * δ⁻¹ * L ^ (-γ + 100 * η) := by have := Real.rpow_pos_of_pos hL (-γ + 100 * η); positivity
        exact mul_le_mul_of_nonneg_left hρ this

end WaveTurbulence.GammaLow.FinalCount.Count
