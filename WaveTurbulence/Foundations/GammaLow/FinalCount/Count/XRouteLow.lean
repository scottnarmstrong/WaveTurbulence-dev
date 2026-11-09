/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.TheoremAX
public import WaveTurbulence.Foundations.FinalCount.OpC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.Pair33
import Mathlib.Tactic

/-! # The X-route of case (4) at `0 < γ ≤ 1/2` (packet L6-COUNT, item C; M2 §4.8 (B), §5.4, §9 "X-route")

The small cell `X = (a=b, c=d, ac, bd, ad, bc)` reached by a complete `(Y2)`-route of the closure `𝕄₁` (main's
`YReachesSmallCell` artifact) is case (I) of Prop 10.4(2)′ at paper level (M2 §5.4): for every bond `ℓ*` of `X`, the
adjacent `(3,3)` or `(3,4)` pair is removed (pair gain `L^{−γ₀}`, M2 §5.1) and the leftover double bond gains
`L^{−η/3}` (Prop 10.2(2)).

* `xMinus_afree_low`: main's `xMinus_afree` for `γ ∈ (0,1)` (its only `γ > 1/2` use was `pairGainAt`).
* `OpCSharpAt`, `OpCSharpInput`, `opCSharpAt`, `opCSharpInput`: operation (c) with the deviation `L^{γ₀}` (sharp
  (operc), M2 Lemma 4.1; F-M2-1, REF-M2 R2: DH23 L1883 bounds the new bond by the sharp count of Lemma A.3(1)). Main's
  `opCAt` proves `L^{γ₀}` and then weakens it to `L^{1−γ}`; `opCSharpAt` omits the weakening.
* `theorem_A_X_low`, `theorem_A_X_one_low`: main's `theorem_A_X`, `theorem_A_X_one` for `γ ∈ (0,1)`, with
  `OpCSharpInput` in place of `OpCInput`. The exponent check (M2 §9: "the arithmetic of `theorem_A_X` must be re-checked
  at γ ≤ 1/2") is `γ₀ + η/200 + η/200 + 2·η/200 + η/200 − γ₀ − η/24 ≤ −η/128`, i.e. `−η/60 ≤ −η/128`, for every γ;
  main's version used `γ₀ = 1 − γ` to cancel `L^{1−γ}` against `L^{−γ₀}`, which fails at `γ < 1/2` (by `1 − 2γ`).

Copied from main `FinalCount/G8R/ThmAOps.lean` (`OpCAt`, `OpCInput`), `FinalCount/OpC.lean` (`opCAt`, `opCInput`),
`FinalCount/XRoute/XMinus.lean`, `FinalCount/XRoute/TheoremAX.lean` (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8

/-- **Operation (c), sharp form** at a fixed `L` (DH23 L1861 with the sharp count of Lemma A.3(1); M2 Lemma 4.1,
F-M2-1 / REF-M2 R2): main's `OpCAt` with the deviation `L^{γ₀}` (`γ₀ = min γ (1−γ)`) in place of `L^{1−γ}`. At
`γ < 1/2`, `L^{1−γ} > L^{γ₀}`, and the X-route arithmetic (`theorem_A_X`, pair gain `L^{−γ₀}`) needs `L^{γ₀}`.

**Deviation (finalcount-g8, session 3).** MOLEPROP4-T's draft statement had no connectivity hypotheses and is false
without them (if `M ∖ Y` is disconnected, `Δχ = 0` and the count gains `L^{d-γ+γ₀}` with no normalization to absorb it).
Added: `M` connected, the chain `Y` connected (`piece M Y`), `M ∖ Y` connected. -/
def OpCSharpAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
    (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
    ∀ (Y Bs : Finset V) (x₁ x₂ : D), Y ⊆ M.atoms → Y ⊆ Bs → (∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1) →
    crossDarts M Y = {x₁, x₂} → M.atom (M.mate x₁) ≠ M.atom (M.mate x₂) →
    (∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b) →
    (∀ a ∈ (Degen.eraseAtoms M Y).atoms, ∀ b ∈ (Degen.eraseAtoms M Y).atoms,
      (Degen.eraseAtoms M Y).SameComponent a b) →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M Bs L γ η P κ ∧
      ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧ κ y ≠ κ y') →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (K * Real.log L ^ B * L ^ min γ (1 - γ)) *
          AFreeSupAdm (Degen.eraseAtoms M Y) d L γ δ C1 (fun P' κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P' κ')

/-- The input: `OpCSharpAt` for every `L ≥ R`. -/
def OpCSharpInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    OpCSharpAt.{u, v} d L γ δ η C1 K B

section
open Set

/-- **Operation (c), sharp form** (main's `opCAt` without its last weakening `L^{γ₀} ≤ L^{1−γ}`). -/
theorem opCSharpAt {d : ℕ} {L γ δ η C1 : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) :
    OpCSharpAt.{u, v} d L γ δ η C1 (2 * 3 ^ d * (d * δ⁻¹ + 1)) 8 := by
  intro V D _ _ _ M hcap hloop hMconn Y Bs x₁ x₂ hYM hYB hch hcross hne hYconn hpost P hP Adm hAdm
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => by
        obtain ⟨y, y', _, _, _, h⟩ := (hAdm κ hκ).2
        exact h (Subsingleton.elim _ _)
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  have hx : x₁ ≠ x₂ := fun h => hne (by rw [h])
  have hY1 : 1 ≤ Y.card := by
    have : x₁ ∈ crossDarts M Y := by rw [hcross]; simp
    exact card_pos.mpr ⟨M.atom x₁, (mem_crossDarts.mp this).1⟩
  let T : Exits2 M := ⟨Y, hYM, x₁, x₂, hcross, hx⟩
  obtain ⟨n, hn, hcount⟩ := countEFree_le_chain M hYM hch hYconn hd hL hδ.1 (γ := γ) Adm (fun κ h => (hAdm κ h).2)
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M Y), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M Y S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M Y), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  have hmonoE : MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M Y Adm) ≤
      MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d)
        (fun κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P κ') :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, hA, _, rfl⟩ := h
      exact lgAdmOff_erase M Bs Y (hAdm κ0 hA).1
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
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (Real.log L ^ 2) ^ 4 = Real.log L ^ (8 : ℝ) := by
      rw [← pow_mul, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW]
    have hWnn : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc (n : ℝ) * (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ)) =
          ((n : ℝ) * L ^ (-((d : ℝ) - γ))) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ) := by ring
      _ ≤ (3 ^ d * (d * δ⁻¹ + 1) * ((1 : ℕ) + 1) * L ^ min γ (1 - γ)) * 1 * Real.log L ^ (8 : ℝ) := by
          refine mul_le_mul (mul_le_mul hnreal hb1 hbpos.le (by positivity)) le_rfl hWnn (by positivity)
      _ = 2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ) := by push_cast; ring
  have hmain : MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ((n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
          (fun κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P κ') P := by
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization]
    calc _ ≤ (((n : ℕ∞) * MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d)
              (fun κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P κ') : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
            MoleProp.freeNormalization (Degen.eraseAtoms M Y) (d := d) L γ δ C1 P) :=
          mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' le_rfl hmonoE)))
            (ENNReal.ofReal_le_ofReal hnorm)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENat.toENNReal_mul, ENat.toENNReal_coe]
          ring
  have h2 : MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
      (fun κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P κ') P ≤
      AFreeSupAdm (Degen.eraseAtoms M Y) d L γ δ C1
        (fun P' κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P' κ') :=
    le_iSup₂_of_le (f := fun P (_ : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms M Y), 0 ≤ P S) =>
      MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
        (fun κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P κ') P) P hPerase le_rfl
  calc MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ _ := hmain
    _ ≤ ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) *
        AFreeSupAdm (Degen.eraseAtoms M Y) d L γ δ C1
          (fun P' κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P' κ') := mul_le_mul' hdev h2

/-- **`OpCSharpInput`** (DH23 L1861, sharp (operc)); any `γ ∈ (0,1)`. -/
theorem opCSharpInput (d : ℕ) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) : OpCSharpInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨2 * 3 ^ d * (d * δ⁻¹ + 1), 8, Real.exp 1, fun L hL => ?_⟩⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  exact @opCSharpAt.{u, v} d L γ δ η C1 hγ hL1 hlog hδ hC1


end

/-- **`xMinus_afree` for every `γ ∈ (0,1)`** (M2 §5.4, the small cell X): main's `xMinus_afree` with
`pairGainAt_all` (its only `γ > 1/2` use was `pairGainAt`). -/
theorem xMinus_afree_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hηγ : η₀ ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η₀ ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsXFinal M →
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        ∀ (e : D) (η' : ℝ), η₀ ≤ η' → ∀ P : Finset V → ℝ,
          (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
          AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤
            ENNReal.ofReal (K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-(η₀ / 3))) := by
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := hγ
  obtain ⟨C102, hC102, h102⟩ := prop102SecondInputSz.{u, v} d hd γ η₀ hγ01 hη₀ hηγ hηs
  refine ⟨C102, hC102, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R102, hR102⟩ := h102 2 C1 hC1 δ hδ
  obtain ⟨K, B, Rp, hRp⟩ := pairGainAt_all.{u, v} hd hγ hδ (by linarith) η₀
  refine ⟨K, B, max (max R102 Rp) (Real.exp 1), fun L hL V D _ _ _ M hX hcap hloop hreg hconn e η' hη' P hP => ?_⟩
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hR1 : R102 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hR2 : Rp ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  obtain ⟨hc4, _, _⟩ := hX.facts hloop
  refine (FinalCountG8.afree_mono_eta _ hL1 hη' P).trans ?_
  refine afree_case_pair hLp (hRp L hR2) (hR102 L hR1) ?_ (hX.isCore hcap hloop hreg hconn) e
    (hX.noTwoCross hloop hreg) (hX.double hloop e) P hP
  rw [hc4]
  push_cast
  nlinarith


section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Theorem A on the X-route, every `γ ∈ (0,1)`** (case-4 note §4; M2 §4.8 (B), §5.4), two β-chains `u → b → v` and
`u′ → b′ → v′`: main's `theorem_A_X` with the sharp operation (c) (`OpCSharpInput`, deviation `L^{γ₀}`) and
`xMinus_afree_low`; the exponent bookkeeping `γ₀ − γ₀ + 5η/200 − η/24 ≤ −η/128` no longer uses `γ₀ = 1 − γ`. -/
theorem theorem_A_X_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (hηs : 4 * 1440061 * η ≤ 1) (hopc : OpCSharpInput.{u, v} d γ η) (hopd : OpDInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), b ∈ M₀.atoms → b' ∈ M₀.atoms → b ≠ b' →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b} = {y₁, y₂} → M₀.out y₁ = false → M₀.out y₂ = true →
        crossDarts M₀ {b'} = {y₃, y₄} → M₀.out y₃ = false → M₀.out y₄ = true →
        M₀.atom (M₀.mate y₁) ≠ M₀.atom (M₀.mate y₂) → M₀.atom (M₀.mate y₃) ≠ M₀.atom (M₀.mate y₄) →
        M₀.atom (M₀.mate y₁) ≠ b' → M₀.atom (M₀.mate y₂) ≠ b' →
        M₀.atom (M₀.mate y₃) ≠ b → M₀.atom (M₀.mate y₄) ≠ b →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b}).atoms,
          (Degen.eraseAtoms M₀ {b}).SameComponent a c) →
        (∀ a ∈ (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).atoms,
          ∀ c ∈ (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).atoms,
          (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).SameComponent a c) →
        (∀ S ∈ MoleProp.ladderCells (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'})
            (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄))),
          GoodCell (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'})
            (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄))) S) →
        ∀ k ≤ 2, YRouteX k (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).outdeg a ≤ 2 ∧
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).indeg a ≤ 2) →
        (∀ z, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom z ≠
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).mate z)) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).deg a = 4) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, ∀ c ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms,
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).SameComponent a c) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y₁ ≠ κ y₂) →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := hγ
  have hg : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hη2 : 0 < η / 2 := by linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨Cc, hCc, hc⟩ := hopc
  obtain ⟨Cd, hCd, hdd⟩ := hopd
  obtain ⟨Cy1, hCy1, hy1⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2) hη2 (by linarith)
  obtain ⟨Cy2, hCy2, hy2⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2 / 2) hη4 (by linarith)
  obtain ⟨Cx, hCx, hx⟩ := xMinus_afree_low.{u, v} d hd γ hγ (η / 8) (by positivity) (by linarith) (by linarith)
  refine ⟨max (max (max Cc Cd) (2 * max Cy1 Cy2)) Cx,
    hCc.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))), fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨⟨⟨e1, e2⟩, e34⟩, e5⟩ := max_le_iff.mp hC1 |>.imp (fun h => max_le_iff.mp h |>.imp max_le_iff.mp id) id
  have e3 : C1 ≥ 2 * Cy1 := by linarith [le_max_left Cy1 Cy2]
  have e4 : C1 ≥ 2 * Cy2 := by linarith [le_max_right Cy1 Cy2]
  obtain ⟨Kc, Bc, Rc, hRc⟩ := hc C1 e1 δ hδ
  obtain ⟨Kd, Bd, Rd, hRd⟩ := hdd C1 e2 δ hδ
  obtain ⟨R1, hR1⟩ := hy1 C1 e3 δ hδ
  obtain ⟨R2, hR2⟩ := hy2 C1 e4 δ hδ
  obtain ⟨K, B, Rx, hRx⟩ := hx C1 e5 δ hδ
  have hθ : 0 < η / 200 := by positivity
  obtain ⟨A1, hA1⟩ := exists_mul_log_rpow_le Kc Bc hθ
  obtain ⟨A2, hA2⟩ := exists_mul_log_rpow_le Kd Bd hθ
  obtain ⟨A3, hA3⟩ := eventually_ylem2Const_le hθ
  obtain ⟨A4, hA4⟩ := exists_mul_log_rpow_le K B hθ
  refine ⟨max Rc (max Rd (max R1 (max R2 (max Rx (max A1 (max A2 (max A3 (max A4 (Real.exp 1))))))))),
    fun L hL => ?_⟩
  simp only [max_le_iff] at hL
  obtain ⟨l1, l2, l3, l4, lx, l6, l7, l8, l9, hLe⟩ := hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-((η / 8) / 3)) := ⟨_, rfl⟩
  intro V D _ _ _ M₀ hcap hloop b b' y₁ y₂ y₃ y₄ hb hb' hbb' hdb hdb' hc1 ho1 ho2 hc2 ho3 ho4 huv huv' hs1 hs2 hs3 hs4 hconn0 hconnb hconnK2 hopenK2
    k hk hroute hcap1 hloop1 h41 hconn1 P hP Adm hAdm
  classical
  -- the chain atoms
  have hy1m : y₁ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_self _ _
  have hy2m : y₂ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hy3m : y₃ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_self _ _
  have hy4m : y₄ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_of_mem (mem_singleton_self _)
  have hat1 : M₀.atom y₁ = b := mem_singleton.mp (mem_crossDarts.mp hy1m).1
  have hat2 : M₀.atom y₂ = b := mem_singleton.mp (mem_crossDarts.mp hy2m).1
  have hat3 : M₀.atom y₃ = b' := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M₀.atom y₄ = b' := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have hu1 : M₀.atom (M₀.mate y₁) ≠ b := fun h => (mem_crossDarts.mp hy1m).2 (by rw [h]; exact mem_singleton_self _)
  have hu2 : M₀.atom (M₀.mate y₂) ≠ b := fun h => (mem_crossDarts.mp hy2m).2 (by rw [h]; exact mem_singleton_self _)
  -- Step 1: operation (c) on the first chain
  have hstep1 := hRc L l1 M₀ hcap hloop hconn0 {b} {b, b'} y₁ y₂ (by simpa using hb) (by simp)
    (fun x hx => by rw [mem_singleton.mp hx]; exact hdb) hc1 huv
    (fun a ha c hc => by rw [mem_singleton.mp ha, mem_singleton.mp hc]; exact Relation.EqvGen.refl _) hconnb
    P hP Adm (fun κ h => ⟨(hAdm κ h).1, y₁, y₂,
      by rw [hat1]; exact mem_singleton_self _, by rw [hat1, hat2], fun h' => (hAdm κ h).2 (by rw [h']),
      (hAdm κ h).2⟩)
  -- the second chain in `𝕄₀ ∖ b`
  have p₃ : M₀.atom y₃ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using hbb'.symm, by simpa using hs3⟩
  have p₄ : M₀.atom y₄ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using hbb'.symm, by simpa using hs4⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hloop hc2 p₃ p₄
  have hbK : b' ∈ (Degen.eraseAtoms M₀ {b}).atoms := mem_sdiff.mpr ⟨hb', by simpa using hbb'.symm⟩
  have hdbK : (Degen.eraseAtoms M₀ {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M₀ {b}).indeg b' = 1 := by
    unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
  -- the atoms of the first chain survive in `𝕄₁ ∖ ℓ`
  set K₂ := Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
    (M₀.atom (M₀.mate y₄)) with hK₂
  have hmemK : ∀ w, w ∈ M₀.atoms → w ≠ b → w ≠ b' → w ∈ K₂.atoms := fun w hw h1 h2 =>
    mem_insert_of_mem (mem_insert_of_mem (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hw, by simpa using h1⟩, by simpa using h2⟩))
  have hu : M₀.atom (M₀.mate y₁) ∈ K₂.atoms := hmemK _ (M₀.atom_mem _) hu1 hs1
  have hv : M₀.atom (M₀.mate y₂) ∈ K₂.atoms := hmemK _ (M₀.atom_mem _) hu2 hs2
  -- Steps 3–4 for `𝕄₁ ∖ ℓ`
  have hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsXFinal M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      ∀ (e : D) (η' : ℝ), η / 8 ≤ η' → ∀ (P : Finset V → ℝ),
        (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
        AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤ ENNReal.ofReal Kt :=
    fun M hX hcapT hloopT hregT hconnT e η' hη' P hP => hKt ▸ hRx L lx M hX hcapT hloopT hregT hconnT e η' hη' P hP
  have hroute' := route_bound_X (η0 := η / 8) (by linarith) (by linarith) hK (hR1 L l3).1 (hR1 L l3).2 (hR2 L l4).1 (hR2 L l4).2 hbase
    (closureTwo M₀ b b' y₁ y₂ y₃ y₄) k hk hroute hcap1 hloop1 h41 hconn1 (Sum.inr true)
  -- Step 2: operation (d) on the second chain, then relabel
  have hsup : AFreeSupAdm (Degen.eraseAtoms M₀ {b}) d L γ δ C1
      (fun P' κ' => lgAdmOff (Degen.eraseAtoms M₀ {b}) ({b, b'} \ {b}) L γ η P' κ') ≤
      ENNReal.ofReal (Kd * Real.log L ^ Bd) * (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 *
        (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal Kt) := by
    refine iSup₂_le fun P' hP' => ?_
    have hu3 : M₀.atom (M₀.mate y₃) ∉ (({b, b'} : Finset V) \ {b}) := by
      simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
      intro h; rcases h with h | h
      · exact absurd h hs3
      · exact absurd h (by simpa using (mem_crossDarts.mp hy3m).2)
    have hu4 : M₀.atom (M₀.mate y₄) ∉ (({b, b'} : Finset V) \ {b}) := by
      simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
      intro h; rcases h with h | h
      · exact absurd h hs4
      · exact absurd h (by simpa using (mem_crossDarts.mp hy4m).2)
    have hopD := hRd L l2 (Degen.eraseAtoms M₀ {b}) (caps_eraseAtoms {b} hcap) (fun z => hloop z.val) hconnb {b'}
      ({b, b'} \ {b}) ⟨y₃, p₃⟩ ⟨y₄, p₄⟩ (by simpa using hbK) (by simp [hbb'.symm]) (by simp)
      (fun x hx => by rw [mem_singleton.mp hx]; exact hdbK) hcK ho3 ho4 huv' hu3 hu4
      (fun a ha c hc => by rw [mem_singleton.mp ha, mem_singleton.mp hc]; exact Relation.EqvGen.refl _)
      hconnK2 hopenK2 P' hP'
      (fun κ' => lgAdmOff (Degen.eraseAtoms M₀ {b}) ({b, b'} \ {b}) L γ η P' κ') (fun κ' h => h)
    refine hopD.trans (mul_le_mul' le_rfl (iSup₂_le fun P'' hP'' => ?_))
    have hB : ∀ x ∈ (({b, b'} : Finset V) \ {b}) \ {b'}, x ∉ K₂.atoms := by
      intro x hx; simp only [mem_sdiff, mem_insert, mem_singleton] at hx; tauto
    refine (countAFree_mono_adm K₂ (L := L) (γ := γ) (δ := δ) (C1 := C1)
      (B := lgAdm K₂ L γ (η / 2) P'') (fun κ' h => lgAdm_of_lgAdmOff hB h)).trans
      ((afree_le_addBond_erase K₂ hu hv L γ δ (η / 2) C1 P'').trans ?_)
    have hcells := ladderCells_addBond_erase K₂ hu hv
    exact hroute' P'' (fun S hS => hP'' S (by show S ∈ MoleProp.ladderCells K₂; rw [← hcells]; exact hS))
  have hc1' : Kc * Real.log L ^ Bc ≤ L ^ (η / 200) := hA1 L l6
  have hc2' : Kd * Real.log L ^ Bd ≤ L ^ (η / 200) := hA2 L l7
  have hc3' := hA3 L l8
  have hc4' : K * Real.log L ^ B ≤ L ^ (η / 200) := hA4 L l9
  have hpos : ∀ x : ℝ, 0 ≤ L ^ x := fun x => Real.rpow_nonneg hLp.le x
  calc MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P
      ≤ ENNReal.ofReal (Kc * Real.log L ^ Bc * L ^ min γ (1 - γ)) * (ENNReal.ofReal (Kd * Real.log L ^ Bd) *
          (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal Kt)) :=
        hstep1.trans (mul_le_mul' le_rfl hsup)
    _ ≤ ENNReal.ofReal (L ^ (η / 200) * L ^ min γ (1 - γ)) * (ENNReal.ofReal (L ^ (η / 200)) *
          (ENNReal.ofReal (L ^ (η / 200)) ^ 2 * ENNReal.ofReal (L ^ (η / 200) * L ^ (-min γ (1 - γ)) *
            L ^ (-((η / 8) / 3))))) := by
        rw [hKt]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc1' (hpos _)))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hc2') (mul_le_mul' (pow_le_pow_left₀ bot_le
            (ENNReal.ofReal_le_ofReal hc3') 2) (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc4' (hpos _)) (hpos _)))))
    _ ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
        rw [← ENNReal.ofReal_pow (hpos _), ← ENNReal.ofReal_mul (pow_nonneg (hpos _) _),
          ← ENNReal.ofReal_mul (hpos _), ← ENNReal.ofReal_mul (mul_nonneg (hpos _) (hpos _))]
        apply ENNReal.ofReal_le_ofReal
        rw [sq]
        simp only [← Real.rpow_add hLp]
        apply Real.rpow_le_rpow_of_exponent_le hL1
        linarith

/-- **Theorem A on the X-route, every `γ ∈ (0,1)`**, one β-chain `u → b → b′ → v` (`σ = 1`): main's `theorem_A_X_one`
with the sharp operation (c) and `xMinus_afree_low`. -/
theorem theorem_A_X_one_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (hηs : 4 * 1440061 * η ≤ 1) (hopc : OpCSharpInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (x₁ x₂ y y' : D), b ∈ M₀.atoms → b' ∈ M₀.atoms →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b, b'} = {x₁, x₂} → M₀.atom (M₀.mate x₁) ≠ M₀.atom (M₀.mate x₂) →
        M₀.atom y = b → M₀.atom y' = b → y ≠ y' →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ ({b, b'} : Finset V), ∀ c ∈ ({b, b'} : Finset V), (piece M₀ {b, b'}).SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms,
          (Degen.eraseAtoms M₀ {b, b'}).SameComponent a c) →
        ∀ k ≤ 2, YRouteX k (closureOne M₀ b b' x₁ x₂) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, (closureOne M₀ b b' x₁ x₂).outdeg a ≤ 2 ∧
          (closureOne M₀ b b' x₁ x₂).indeg a ≤ 2) →
        (∀ z, (closureOne M₀ b b' x₁ x₂).atom z ≠ (closureOne M₀ b b' x₁ x₂).atom ((closureOne M₀ b b' x₁ x₂).mate z)) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, (closureOne M₀ b b' x₁ x₂).deg a = 4) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, ∀ c ∈ (closureOne M₀ b b' x₁ x₂).atoms,
          (closureOne M₀ b b' x₁ x₂).SameComponent a c) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y ≠ κ y') →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := hγ
  have hg : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hη2 : 0 < η / 2 := by linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨Cc, hCc, hc⟩ := hopc
  obtain ⟨Cy1, hCy1, hy1⟩ := ylem2At_of.{u, v} d hd γ hγ0 η hη hηmax
  obtain ⟨Cy2, hCy2, hy2⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2) hη2 (by linarith)
  obtain ⟨Cx, hCx, hx⟩ := xMinus_afree_low.{u, v} d hd γ hγ (η / 8) (by positivity) (by linarith) (by linarith)
  refine ⟨max (max Cc (2 * max Cy1 Cy2)) Cx, hCc.trans ((le_max_left _ _).trans (le_max_left _ _)),
    fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨⟨e1, e34⟩, e5⟩ := max_le_iff.mp hC1 |>.imp max_le_iff.mp id
  have e3 : C1 ≥ 2 * Cy1 := by linarith [le_max_left Cy1 Cy2]
  have e4 : C1 ≥ 2 * Cy2 := by linarith [le_max_right Cy1 Cy2]
  obtain ⟨Kc, Bc, Rc, hRc⟩ := hc C1 e1 δ hδ
  obtain ⟨R1, hR1⟩ := hy1 C1 e3 δ hδ
  obtain ⟨R2, hR2⟩ := hy2 C1 e4 δ hδ
  obtain ⟨K, B, Rx, hRx⟩ := hx C1 e5 δ hδ
  have hθ : 0 < η / 200 := by positivity
  obtain ⟨A1, hA1⟩ := exists_mul_log_rpow_le Kc Bc hθ
  obtain ⟨A3, hA3⟩ := eventually_ylem2Const_le hθ
  obtain ⟨A4, hA4⟩ := exists_mul_log_rpow_le K B hθ
  refine ⟨max Rc (max R1 (max R2 (max Rx (max A1 (max A3 (max A4 (Real.exp 1))))))), fun L hL => ?_⟩
  simp only [max_le_iff] at hL
  obtain ⟨l1, l3, l4, lx, l6, l8, l9, hLe⟩ := hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-((η / 8) / 3)) := ⟨_, rfl⟩
  intro V D _ _ _ M₀ hcap hloop b b' x₁ x₂ y y' hb hb' hdb hdb' hc1 huv hy hy' hyy' hconn0 hYconn hconnK k hk hroute hcap1 hloop1 h41
    hconn1 P hP Adm hAdm
  classical
  have hx1m : x₁ ∈ crossDarts M₀ {b, b'} := by rw [hc1]; exact mem_insert_self _ _
  have hx2m : x₂ ∈ crossDarts M₀ {b, b'} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hY : ({b, b'} : Finset V) ⊆ M₀.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  -- Step 1: operation (c) on the chain
  have hstep1 := hRc L l1 M₀ hcap hloop hconn0 {b, b'} {b, b'} x₁ x₂ hY (subset_refl _)
    (fun z hz => by simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
    hc1 huv hYconn hconnK P hP Adm (fun κ h => ⟨(hAdm κ h).1, y, y', by rw [hy]; exact mem_insert_self _ _, by rw [hy, hy'],
      hyy', (hAdm κ h).2⟩)
  set K₂ := Degen.eraseAtoms M₀ {b, b'} with hK₂
  have hu : M₀.atom (M₀.mate x₁) ∈ K₂.atoms := mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx1m).2⟩
  have hv : M₀.atom (M₀.mate x₂) ∈ K₂.atoms := mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx2m).2⟩
  have hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsXFinal M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      ∀ (e : D) (η' : ℝ), η / 8 ≤ η' → ∀ (P : Finset V → ℝ),
        (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
        AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤ ENNReal.ofReal Kt :=
    fun M hX hcapT hloopT hregT hconnT e η' hη' P hP => hKt ▸ hRx L lx M hX hcapT hloopT hregT hconnT e η' hη' P hP
  have hroute' := route_bound_X (η0 := η / 8) (by linarith) (by linarith) hK (hR1 L l3).1 (hR1 L l3).2 (hR2 L l4).1 (hR2 L l4).2 hbase
    (closureOne M₀ b b' x₁ x₂) k hk hroute hcap1 hloop1 h41 hconn1 (Sum.inr true)
  have hsup : AFreeSupAdm K₂ d L γ δ C1 (fun P' κ' => lgAdmOff K₂ ({b, b'} \ {b, b'}) L γ η P' κ') ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
        ENNReal.ofReal Kt := by
    refine iSup₂_le fun P' hP' => ?_
    have hB : ∀ z ∈ ({b, b'} : Finset V) \ {b, b'}, z ∉ K₂.atoms := by
      intro z hz; simp at hz
    refine (countAFree_mono_adm K₂ (L := L) (γ := γ) (δ := δ) (C1 := C1)
      (B := lgAdm K₂ L γ η P') (fun κ' h => lgAdm_of_lgAdmOff hB h)).trans
      ((afree_le_addBond_erase K₂ hu hv L γ δ η C1 P').trans ?_)
    have hcells := ladderCells_addBond_erase K₂ hu hv
    exact hroute' P' (fun S hS => hP' S (by show S ∈ MoleProp.ladderCells K₂; rw [← hcells]; exact hS))
  have hc1' : Kc * Real.log L ^ Bc ≤ L ^ (η / 200) := hA1 L l6
  have hc3' := hA3 L l8
  have hc4' : K * Real.log L ^ B ≤ L ^ (η / 200) := hA4 L l9
  have hpos : ∀ x : ℝ, 0 ≤ L ^ x := fun x => Real.rpow_nonneg hLp.le x
  calc MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P
      ≤ ENNReal.ofReal (Kc * Real.log L ^ Bc * L ^ min γ (1 - γ)) *
          (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal Kt) :=
        hstep1.trans (mul_le_mul' le_rfl hsup)
    _ ≤ ENNReal.ofReal (L ^ (η / 200) * L ^ min γ (1 - γ)) *
          (ENNReal.ofReal (L ^ (η / 200)) ^ 2 * ENNReal.ofReal (L ^ (η / 200) * L ^ (-min γ (1 - γ)) *
            L ^ (-((η / 8) / 3)))) := by
        rw [hKt]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc1' (hpos _)))
          (mul_le_mul' (pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hc3') 2) (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc4' (hpos _)) (hpos _))))
    _ ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
        rw [← ENNReal.ofReal_pow (hpos _), ← ENNReal.ofReal_mul (pow_nonneg (hpos _) _),
          ← ENNReal.ofReal_mul (mul_nonneg (hpos _) (hpos _))]
        apply ENNReal.ofReal_le_ofReal
        rw [sq]
        simp only [← Real.rpow_add hLp]
        apply Real.rpow_le_rpow_of_exponent_le hL1
        linarith


end

end WaveTurbulence.GammaLow.FinalCount.Count
