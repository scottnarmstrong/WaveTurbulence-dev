/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.BiBridgeRank
public import WaveTurbulence.Foundations.FinalCount.BiBridgeReal
public import WaveTurbulence.Foundations.FinalCount.BetaCut
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
import Mathlib.Tactic

/-! # `BiBridgeInput` (DH23 L1967, Lemma A.3(1))

A set `S` attached by two bonds of opposite directions with `k_{ℓ₁} ≠ k_{ℓ₂}`:
`𝔄(𝕄) ≤ K (log L)^8 (|𝕄|+1) L^{γ₀} 𝔄(𝕄[S]) 𝔄(𝕄[S^c])`, `K = 3^d (dδ⁻¹ + 1)`.
The factor `L^{γ₀}` is the strip count of `k_{ℓ₁}` in the unit ball (`BiBridgeCount`, `bibridge_n_bound`), `Δχ = +1`.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem norm_split1 {L a b : ℝ} (hL : 0 < L) (hb : 0 < b) {χP χE : ℤ} {cM cP cE W : ℝ} (hcP : 0 ≤ cP)
    (hcE : 0 ≤ cE) (hc : cM ≤ cP * cE * W) :
    L ^ (-a * ((χP + χE + 1 : ℤ) : ℝ)) * b ^ (χP + χE + 1) * cM ≤
      (L ^ (-a) * b * W) * ((L ^ (-a * χP) * b ^ χP * cP) * (L ^ (-a * χE) * b ^ χE * cE)) := by
  have hLb : 0 < L ^ (-a * ((χP + χE + 1 : ℤ) : ℝ)) * b ^ (χP + χE + 1) := by positivity
  have e : L ^ (-a * ((χP + χE + 1 : ℤ) : ℝ)) * b ^ (χP + χE + 1) =
      (L ^ (-a) * b) * ((L ^ (-a * χP) * b ^ χP) * (L ^ (-a * χE) * b ^ χE)) := by
    push_cast
    rw [mul_add, mul_add, mul_one, Real.rpow_add hL, Real.rpow_add hL, zpow_add₀ hb.ne', zpow_add₀ hb.ne',
      zpow_one]
    ring
  calc _ ≤ L ^ (-a * ((χP + χE + 1 : ℤ) : ℝ)) * b ^ (χP + χE + 1) * (cP * cE * W) :=
        mul_le_mul_of_nonneg_left hc hLb.le
    _ = _ := by rw [e]; ring

/-- **`BiBridgeAt`** with `K = 3^d (dδ⁻¹ + 1)`, `B = 8`. -/
theorem biBridgeAt {d : ℕ} {L γ δ η C1 : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) :
    BiBridgeAt.{u, v} d L γ δ η C1 (3 ^ d * (d * δ⁻¹ + 1)) 8 := by
  intro V D _ _ _ M hcap hloop S x₁ x₂ hS hcross hne hout hconn hconnS hconnT P hP Adm hAdm
  classical
  have hLp : 0 < L := by linarith
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- no decorations
    have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => (hAdm κ hκ).2 (Subsingleton.elim _ _)
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  let T : Exits2 M := ⟨S, hS, x₁, x₂, hcross, hne⟩
  obtain ⟨n, hn, hcount⟩ := T.countEFree_le_bi (d := d) (L := L) (γ := γ) (δ := δ) (η := η) hout hd hL hδ.1 P Adm hAdm
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M S), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M S), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M S S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hmonoE : MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M S Adm) ≤
      MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms M S) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, hA, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase M L γ η 0 _ (hAdm κ0 hA).1.1,
        MoleProp.cellGapRestriction_erase M L 0 _ P _ (hAdm κ0 hA).1.2⟩
  -- components
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨M.atom x₁, M.atom_mem x₁⟩ hconn
  have hFp : (piece M S).numComponents = 1 := Mole.numComponents_eq_one (piece M S)
    (by rw [piece_atoms hS]; exact ⟨M.atom x₁, T.atom_x⟩) (by rw [piece_atoms hS]; exact hconnS)
  have hY : M.atoms \ (M.atoms \ S) = S := by rw [_root_.sdiff_sdiff_right_self, inf_eq_right.mpr hS]
  have hFe : (Degen.eraseAtoms M S).numComponents = 1 := by
    refine Mole.numComponents_eq_one (Degen.eraseAtoms M S) ⟨M.atom (M.mate x₁), ?_⟩ ?_
    · exact mem_sdiff.mpr ⟨M.atom_mem _, (mem_crossDarts.mp T.x_mem).2⟩
    · intro a ha b hb
      exact (sameComponent_erase_congr M hY a b).mp (hconnT a ha b hb)
  have hrk := T.circuitRank_eq4 hF1 hFp hFe
  have hcp := T.cellProduct_le4 hloop hdeg (L := L) (γ := γ) (δ := δ) hLp.le hδ.1.le hlog P hP
  have hbpos : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < C1 := by linarith
    have := hδ.1; positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hC : 0 < C1 := by linarith
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by have := hδ.1; positivity) zero_le_one
      _ = 1 := one_mul 1
  have np := MoleProp.freeNormalization_pos (piece M S) (d := d) (γ := γ) hLp hδ.1 (by linarith : 0 < C1)
    hlog0 P hPpiece
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms M S) (d := d) (γ := γ) hLp hδ.1
    (by linarith : 0 < C1) hlog0 P hPerase
  have hcpP : 0 ≤ MoleProp.cellProduct (piece M S) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPpiece).le
  have hcpE : 0 ≤ MoleProp.cellProduct (Degen.eraseAtoms M S) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
        (MoleProp.freeNormalization (piece M S) (d := d) L γ δ C1 P *
          MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P) := by
    unfold MoleProp.freeNormalization
    rw [hrk]
    exact norm_split1 hLp hbpos hcpP hcpE hcp
  have hmain : MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ((n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4)) *
        (AFree (piece M S) d L γ δ η C1 P * AFree (Degen.eraseAtoms M S) d L γ δ η C1 P) := by
    rw [MoleProp.countAFree_eq_normalization]
    unfold AFree
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization]
    calc _ ≤ (((n : ℕ∞) * MoleProp.countEFree (piece M S) L γ δ (0 : Mom d) (lgAdm (piece M S) L γ η P) *
            MoleProp.countEFree (Degen.eraseAtoms M S) L γ δ (0 : Mom d)
              (lgAdm (Degen.eraseAtoms M S) L γ η P) : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
            (MoleProp.freeNormalization (piece M S) (d := d) L γ δ C1 P *
              MoleProp.freeNormalization (Degen.eraseAtoms M S) (d := d) L γ δ C1 P)) :=
          mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' le_rfl hmonoE)))
            (ENNReal.ofReal_le_ofReal hnorm)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul np.le, ENat.toENNReal_mul,
            ENat.toENNReal_mul, ENat.toENNReal_coe]
          ring
  have h1 := afree_le_afreeSup (piece M S) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) P hPpiece
  have h2 := afree_le_afreeSup (Degen.eraseAtoms M S) (d := d) (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1)
    P hPerase
  have h4 : AFreeSup (Degen.eraseAtoms M S) d L γ δ η C1 = AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1 :=
    afreeSup_erase_congr M (d := d) (A := S) (B := M.atoms \ (M.atoms \ S)) hY.symm L γ δ η C1
  -- the real estimate
  have hnreal := bibridge_n_bound (n := (n : ℝ)) (L := L) (δ := δ) (γ := γ) (d := d) (s := S.card) hL hδ.1
    hγ.1 hγ.2 hd (Nat.cast_nonneg _) hn
  have hscard : (S.card : ℝ) ≤ M.atoms.card := by exact_mod_cast Finset.card_le_card hS
  have hdev : (n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (M.atoms.card + 1) *
        L ^ min γ (1 - γ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (Real.log L ^ 2) ^ 4 = Real.log L ^ (8 : ℝ) := by
      rw [← pow_mul, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW]
    have hWnn : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hK : 0 ≤ (3 : ℝ) ^ d * (d * δ⁻¹ + 1) := by have := hδ.1; positivity
    calc (n : ℝ) * (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ)) =
          ((n : ℝ) * L ^ (-((d : ℝ) - γ))) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ) := by ring
      _ ≤ (3 ^ d * (d * δ⁻¹ + 1) * (S.card + 1) * L ^ min γ (1 - γ)) * 1 * Real.log L ^ (8 : ℝ) := by
          refine mul_le_mul (mul_le_mul hnreal hb1 hbpos.le (by positivity)) le_rfl hWnn (by positivity)
      _ ≤ 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (M.atoms.card + 1) * L ^ min γ (1 - γ) := by
          have hLm : 0 ≤ L ^ min γ (1 - γ) := Real.rpow_nonneg hLp.le _
          have : (S.card + 1 : ℝ) ≤ M.atoms.card + 1 := by linarith
          calc _ = 3 ^ d * (d * δ⁻¹ + 1) * (S.card + 1) * L ^ min γ (1 - γ) * Real.log L ^ (8 : ℝ) := by ring
            _ ≤ 3 ^ d * (d * δ⁻¹ + 1) * (M.atoms.card + 1) * L ^ min γ (1 - γ) * Real.log L ^ (8 : ℝ) := by
                gcongr
            _ = _ := by ring
  rw [← h4]
  calc MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ _ := hmain
    _ ≤ ENNReal.ofReal (3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (M.atoms.card + 1) *
        L ^ min γ (1 - γ)) *
        (AFreeSup (piece M S) d L γ δ η C1 * AFreeSup (Degen.eraseAtoms M S) d L γ δ η C1) :=
        mul_le_mul' hdev (mul_le_mul' h1 h2)
    _ = _ := by ring

/-- **`BiBridgeInput`** (DH23 L1967), for `γ ∈ (0,1)`. -/
theorem biBridgeInput (d : ℕ) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) : BiBridgeInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨3 ^ d * (d * δ⁻¹ + 1), 8, Real.exp 1, fun L hL => ?_⟩⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  exact @biBridgeAt.{u, v} d L γ δ η C1 hγ hL1 hlog hδ hC1

end WaveTurbulence.FinalCountG8
