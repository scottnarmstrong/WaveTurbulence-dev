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
