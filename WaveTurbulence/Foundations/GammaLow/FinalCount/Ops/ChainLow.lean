/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainRemoval96
import Mathlib.Tactic

/-! # Operation (c) at `0 < γ ≤ 1/2` (packet L6, item D; M2 Lemma 4.1, F-M2-1)

* `opC_triv`: operation (c) with the trivial branch of DH23 Lemma A.3(1), `𝔄(𝕄) ≤ 3^d L^γ (log L)^8 · 𝔄(𝕄 ∖ Y)`
  (one free vector in a unit ball: `n ≤ (2L+1)^d`, the left branch of `countEFree_le_chain_rho`). Together with main's
  `opC_rho` this is the sharp (operc) `L^{γ−1} + δ⁻¹ min(R⁻¹L^{−γ}, L^{γ})` of M2 Lemma 4.1 (needed in case (2) and in
  case (4)′ class 2 at `γ < 1/2`, erratum F-M2-1 / REF-M2 R2).
* `chain_A_bound_low`: main's `chain_A_bound` for every `γ ∈ (0, 1)` (its `1/2 < γ` was used only for `γ ∈ (0, 1)`).
* `chain_A_bound_triv`: the same with `opC_triv`.

Copied from main `FinalCount/OpCRho.lean` and `FinalCount/ChainRemoval96.lean` (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.FinalCountG8.P101

theorem opC_triv {d : ℕ} {L γ δ C1 ρ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (hρ : 0 < ρ)
    {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hMconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (Y : Finset V) (x₁ x₂ : D) (hYM : Y ⊆ M.atoms) (hch : ∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hcross : crossDarts M Y = {x₁, x₂}) (hne : M.atom (M.mate x₁) ≠ M.atom (M.mate x₂))
    (hYconn : ∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b)
    (hpost : ∀ a ∈ (Degen.eraseAtoms M Y).atoms, ∀ b ∈ (Degen.eraseAtoms M Y).atoms,
      (Degen.eraseAtoms M Y).SameComponent a b)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility M Y Adm) P := by
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => by
        obtain ⟨y, y', _, _, _, h⟩ := hAdm κ hκ
        have := Subsingleton.elim (Molecule.kvec L (0 : Mom 0) κ y) (Molecule.kvec L (0 : Mom 0) κ y')
        rw [this, sub_self, norm_zero] at h
        linarith
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  have hx : x₁ ≠ x₂ := fun h => hne (by rw [h])
  have hY1 : 1 ≤ Y.card := by
    have : x₁ ∈ crossDarts M Y := by rw [hcross]; simp
    exact card_pos.mpr ⟨M.atom x₁, (mem_crossDarts.mp this).1⟩
  let T : Exits2 M := ⟨Y, hYM, x₁, x₂, hcross, hx⟩
  obtain ⟨n, hn, hcount⟩ := countEFree_le_chain_rho M hYM hch hYconn hd hL hδ.1 (γ := γ) ρ hρ Adm hAdm
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
  have hdev : (n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) ≤
      ENNReal.ofReal (3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (Real.log L ^ 2) ^ 4 = Real.log L ^ (8 : ℝ) := by
      rw [← pow_mul, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW]
    have hWnn : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hn1 : (n : ℝ) ≤ (2 * L + 1) ^ d := hn.trans (min_le_left _ _)
    have h3 : (2 * L + 1) ^ d ≤ 3 ^ d * L ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpow : L ^ d * L ^ (-((d : ℝ) - γ)) = L ^ γ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hLp]; congr 1; ring
    have hb' : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hLp.le _
    calc (n : ℝ) * (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ))
        ≤ (3 ^ d * L ^ d) * (L ^ (-((d : ℝ) - γ)) * 1 * Real.log L ^ (8 : ℝ)) := by
          refine mul_le_mul (hn1.trans h3) ?_ (mul_nonneg (mul_nonneg hb' hbpos.le) hWnn)
            (mul_nonneg (by positivity) (pow_nonneg hLp.le _))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 hb') hWnn
      _ = 3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ) := by rw [← hpow]; ring
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
  calc MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ _ := hmain
    _ ≤ _ := mul_le_mul' hdev le_rfl


theorem chain_A_bound_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀, ∀ ρ : ℝ, 0 < ρ →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
        ∀ K, IsChainSet M cls K →
          (∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
            ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) →
          M.countA L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) := by
  classical
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨Rp, hRp⟩ := hP1 C1 hC1 δ hδ
  refine ⟨max Rp (Real.exp 1), le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _), ?_⟩
  intro L hL ρ hρ V D _ _ _ M cls odd Adm P hS hF hnodd hnc hP hMA K hK hAdm
  have hLRp : Rp ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hM : M.IsMolecule := hS.isMolecule
  have hC1' : 1 ≤ C1 := le_trans hCs hC1
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  -- the chain data
  obtain ⟨y₁, y₂, hcross, hy12, hε1, hε2, hne⟩ := hS.chains hnodd hnc K hK
  have hKA : K ⊆ M.atoms := hK.2.1
  have hch : ∀ b ∈ K, M.outdeg b = 1 ∧ M.indeg b = 1 := by
    intro b hb
    have hnE : ¬ (cls b).IsEps := hK.2.2.1 b hb
    have h2 : M.deg b ≤ 2 := (hS.classes b (hKA hb)).mpr hnE
    have h4 : M.deg b = 2 ∨ M.deg b = 4 := hS.evenDeg hnodd b (hKA hb)
    exact hS.dir2 b (hKA hb) (by omega)
  have hcard : (crossDarts M K).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun a ha => by
    rcases hS.evenDeg hnodd a ha with h | h <;> omega) K hcard
  have hAdm'' : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
        ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := fun κ hκ => hAdm κ hκ.1
  have hstep := opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := ρ) hγ01 hL1 hlog hδ hC1' hρ M hS.caps hS.noLoop
    hS.conn K y₁ y₂ hKA hch hcross hne (chain_piece_connected hK) hpost P' (fun S _ => hP _)
    (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) hAdm''
  -- Prop 10.1' on the remainder
  have hKne : K.Nonempty := hK.1
  have hPM : PMol (nonEps M.atoms cls) (Degen.eraseAtoms M K) :=
    pmol_erase_of_connected hS.caps (fun v hv hvB => (hS.classes v hv).mpr (mem_filter.mp hvB).2) hS.conn K hKA hKne
  have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
    intro κ hκ v hvB x y hx hy hxy
    have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
    have hε : (cls v).IsEps := by
      by_contra hne'; exact hvB (mem_filter.mpr ⟨hv, hne'⟩)
    exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
  have hrest : MoleProp.countAFree (Degen.eraseAtoms M K) L γ δ C1 (0 : Mom d)
      (erasedFreeAdmissibility M K (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)) P' ≤ 1 :=
    hRp L hLRp hlog (nonEps M.atoms cls) (Degen.eraseAtoms M K) hPM (fun x _ => hS.noLoop x.val) _ _
      (projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K _ hLG)
      (projected_cellGap M L (0 : Mom d) K _ P' (fun κ hκ => hκ.2))
      (fun S _ => hP _)
  calc _ ≤ _ := hstep
    _ ≤ ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) * 1 :=
        mul_le_mul' le_rfl hrest
    _ = _ := mul_one _


theorem chain_A_bound_triv (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀, ∀ ρ : ℝ, 0 < ρ →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
        ∀ K, IsChainSet M cls K →
          (∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
            ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) →
          M.countA L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ)) := by
  classical
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨Rp, hRp⟩ := hP1 C1 hC1 δ hδ
  refine ⟨max Rp (Real.exp 1), le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _), ?_⟩
  intro L hL ρ hρ V D _ _ _ M cls odd Adm P hS hF hnodd hnc hP hMA K hK hAdm
  have hLRp : Rp ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hM : M.IsMolecule := hS.isMolecule
  have hC1' : 1 ≤ C1 := le_trans hCs hC1
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  -- the chain data
  obtain ⟨y₁, y₂, hcross, hy12, hε1, hε2, hne⟩ := hS.chains hnodd hnc K hK
  have hKA : K ⊆ M.atoms := hK.2.1
  have hch : ∀ b ∈ K, M.outdeg b = 1 ∧ M.indeg b = 1 := by
    intro b hb
    have hnE : ¬ (cls b).IsEps := hK.2.2.1 b hb
    have h2 : M.deg b ≤ 2 := (hS.classes b (hKA hb)).mpr hnE
    have h4 : M.deg b = 2 ∨ M.deg b = 4 := hS.evenDeg hnodd b (hKA hb)
    exact hS.dir2 b (hKA hb) (by omega)
  have hcard : (crossDarts M K).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun a ha => by
    rcases hS.evenDeg hnodd a ha with h | h <;> omega) K hcard
  have hAdm'' : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
        ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := fun κ hκ => hAdm κ hκ.1
  have hstep := opC_triv (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := ρ) hγ01 hL1 hlog hδ hC1' hρ M hS.caps hS.noLoop
    hS.conn K y₁ y₂ hKA hch hcross hne (chain_piece_connected hK) hpost P' (fun S _ => hP _)
    (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) hAdm''
  -- Prop 10.1' on the remainder
  have hKne : K.Nonempty := hK.1
  have hPM : PMol (nonEps M.atoms cls) (Degen.eraseAtoms M K) :=
    pmol_erase_of_connected hS.caps (fun v hv hvB => (hS.classes v hv).mpr (mem_filter.mp hvB).2) hS.conn K hKA hKne
  have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
    intro κ hκ v hvB x y hx hy hxy
    have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
    have hε : (cls v).IsEps := by
      by_contra hne'; exact hvB (mem_filter.mpr ⟨hv, hne'⟩)
    exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
  have hrest : MoleProp.countAFree (Degen.eraseAtoms M K) L γ δ C1 (0 : Mom d)
      (erasedFreeAdmissibility M K (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)) P' ≤ 1 :=
    hRp L hLRp hlog (nonEps M.atoms cls) (Degen.eraseAtoms M K) hPM (fun x _ => hS.noLoop x.val) _ _
      (projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K _ hLG)
      (projected_cellGap M L (0 : Mom d) K _ P' (fun κ hκ => hκ.2))
      (fun S _ => hP _)
  calc _ ≤ _ := hstep
    _ ≤ ENNReal.ofReal (3 ^ d * L ^ γ * Real.log L ^ (8 : ℝ)) * 1 :=
        mul_le_mul' le_rfl hrest
    _ = _ := mul_one _

end WaveTurbulence.GammaLow.FinalCount
