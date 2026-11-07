/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpC
import Mathlib.Tactic

/-! # Operation (c), decoration level (finalcount-g8, F6-1)

`opCFree`: `𝔄(𝕄; Adm) ≤ K (log L)^8 L^{1-γ} · 𝔄(𝕄 ∖ Y; erasedFreeAdmissibility 𝕄 Y Adm)` for a connected chain `Y`
(`in = out = 1`) with one nonzero gap in every `Adm`-decoration. Clone of `opCAt` that keeps the projected admissibility
instead of weakening it to `lgAdmOff`.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem opCFree {d : ℕ} {L γ δ C1 : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hMconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (Y : Finset V) (x₁ x₂ : D) (hYM : Y ⊆ M.atoms) (hch : ∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hcross : crossDarts M Y = {x₁, x₂}) (hne : M.atom (M.mate x₁) ≠ M.atom (M.mate x₂))
    (hYconn : ∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b)
    (hpost : ∀ a ∈ (Degen.eraseAtoms M Y).atoms, ∀ b ∈ (Degen.eraseAtoms M Y).atoms,
      (Degen.eraseAtoms M Y).SameComponent a b)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧ κ y ≠ κ y') :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d) (MoleProp.erasedFreeAdmissibility M Y Adm) P := by
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => by
        obtain ⟨y, y', _, _, _, h⟩ := hAdm κ hκ
        exact h (Subsingleton.elim _ _)
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  have hx : x₁ ≠ x₂ := fun h => hne (by rw [h])
  have hY1 : 1 ≤ Y.card := by
    have : x₁ ∈ crossDarts M Y := by rw [hcross]; simp
    exact card_pos.mpr ⟨M.atom x₁, (mem_crossDarts.mp this).1⟩
  let T : Exits2 M := ⟨Y, hYM, x₁, x₂, hcross, hx⟩
  obtain ⟨n, hn, hcount⟩ := countEFree_le_chain M hYM hch hYconn hd hL hδ.1 (γ := γ) Adm hAdm
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M Y), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M Y S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M Y), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  -- ranks
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨M.atom x₁, M.atom_mem x₁⟩ hMconn
  have hFp : (piece M Y).numComponents = 1 := Mole.numComponents_eq_one (piece M Y)
    (by rw [piece_atoms hYM]; exact ⟨M.atom x₁, T.atom_x⟩) (by rw [piece_atoms hYM]; exact hYconn)
  have hFe : (Degen.eraseAtoms M Y).numComponents = 1 :=
    Mole.numComponents_eq_one (Degen.eraseAtoms M Y) ⟨M.atom (M.mate x₁), mem_sdiff.mpr
      ⟨M.atom_mem _, (mem_crossDarts.mp T.x_mem).2⟩⟩ hpost
  have hrk := T.circuitRank_eq4 hF1 hFp hFe
  have hrkp : (piece M Y).circuitRank = 0 := by
    unfold Molecule.circuitRank
    rw [chain_piece_card M hYM hch hY1 hcross hx, piece_atoms hYM, hFp]
    push_cast; ring
  rw [hrkp, zero_add] at hrk
  -- cells
  have hcellsP : MoleProp.ladderCells (piece M Y) = ∅ := by
    rw [T.ladderCells_piece_eq']
    refine eq_empty_of_forall_notMem fun S hS => ?_
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    have hS3 := (mem_filter.mp hS1).2
    refine no_cell_of_deg_le_two M hS3 fun a ha => ?_
    have := Mole.outdeg_add_indeg M a; have := hch a (hS2 ha); omega
  have hcp := T.cellProduct_le4 hloop hdeg (L := L) (γ := γ) (δ := δ) hLp.le hδ.1.le hlog P hP
  have hcpP : MoleProp.cellProduct (piece M Y) L γ δ P = 1 := by
    unfold MoleProp.cellProduct; rw [hcellsP]; simp
  have hcp' : MoleProp.cellProduct M L γ δ P ≤
      MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ 4 := by
    have h := hcp
    change MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct (piece M Y) L γ δ P *
      MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ 4 at h
    rwa [hcpP, one_mul] at h
  have hbpos : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < C1 := by linarith
    have := hδ.1; positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hC : 0 < C1 := by linarith
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by have := hδ.1; positivity) zero_le_one
      _ = 1 := one_mul 1
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms M Y) (d := d) (γ := γ) hLp hδ.1
    (by linarith : 0 < C1) hlog0 P hPerase
  have hcpE : 0 ≤ MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
        MoleProp.freeNormalization (Degen.eraseAtoms M Y) (d := d) L γ δ C1 P := by
    have := norm_split1 (a := (d : ℝ) - γ) (χP := 0) (χE := (Degen.eraseAtoms M Y).circuitRank) hLp hbpos
      (cP := 1) (cE := MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P) (cM := MoleProp.cellProduct M L γ δ P)
      (W := (Real.log L ^ 2) ^ 4) zero_le_one hcpE (by simpa using hcp')
    unfold MoleProp.freeNormalization
    rw [hrk]
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using this
  have hnreal := bibridge_n_bound (n := (n : ℝ)) (L := L) (δ := δ) (γ := γ) (d := d) (s := 1) hL hδ.1
    hγ.1 hγ.2 hd (Nat.cast_nonneg _) (by simpa using hn)
  have hdev : (n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (Real.log L ^ 2) ^ 4 = Real.log L ^ (8 : ℝ) := by
      rw [← pow_mul, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW]
    have hWnn : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hLm : L ^ min γ (1 - γ) ≤ L ^ (1 - γ) := Real.rpow_le_rpow_of_exponent_le hL (min_le_right _ _)
    calc (n : ℝ) * (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ)) =
          ((n : ℝ) * L ^ (-((d : ℝ) - γ))) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ) := by ring
      _ ≤ (3 ^ d * (d * δ⁻¹ + 1) * ((1 : ℕ) + 1) * L ^ min γ (1 - γ)) * 1 * Real.log L ^ (8 : ℝ) := by
          refine mul_le_mul (mul_le_mul hnreal hb1 hbpos.le (by positivity)) le_rfl hWnn (by positivity)
      _ ≤ 2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ) := by
          have hK : 0 ≤ (3 : ℝ) ^ d * (d * δ⁻¹ + 1) := by have := hδ.1; positivity
          calc _ = 2 * (3 ^ d * (d * δ⁻¹ + 1)) * L ^ min γ (1 - γ) * Real.log L ^ (8 : ℝ) := by push_cast; ring
            _ ≤ 2 * (3 ^ d * (d * δ⁻¹ + 1)) * L ^ (1 - γ) * Real.log L ^ (8 : ℝ) := by gcongr
            _ = _ := by ring
  have hmain : MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ((n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility M Y Adm) P := by
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization]
    calc _ ≤ (((n : ℕ∞) * MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d)
              (MoleProp.erasedFreeAdmissibility M Y Adm) : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
            MoleProp.freeNormalization (Degen.eraseAtoms M Y) (d := d) L γ δ C1 P) :=
          mul_le_mul' (ENat.toENNReal_mono hcount)
            (ENNReal.ofReal_le_ofReal hnorm)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENat.toENNReal_mul, ENat.toENNReal_coe]
          ring
  exact hmain.trans (mul_le_mul' hdev le_rfl)

end WaveTurbulence.FinalCountG8
