/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpDCount
public import WaveTurbulence.Foundations.FinalCount.OpC
import Mathlib.Tactic

/-! # `OpDInput` (DH23 L1865-L1867): replacing a chain by one bond

`𝔄(𝕄) ≤ K (log L)^{14} 𝔄(𝕄 ∖ Y + (u → v))` for a connected chain `Y` (at most three atoms, `in = out = 1`) between distinct
atoms `u, v` outside the exempt set; LG is weakened from `η` to `η/2`. `Δχ = 0`. The constant is
`5 (1 + 4·3)² · 25 = 21125`.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem opDAt {d : ℕ} {L γ δ η C1 : ℝ} (hη : 0 < η) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hL11 : 11 ≤ L ^ (η / 2))
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) :
    OpDAt.{u, v} d L γ δ η C1 21125 14 := by
  intro V D _ _ _ M hcap hloop hMconn Y Bs x₁ x₂ hYM hYB hY3 hch hcross ho1 ho2 hne hu hv hYconn hpost hopen P hP Adm hAdm
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have hx : x₂ ≠ x₁ := fun h => hne (by rw [h])
  have hcross' : crossDarts M Y = {x₂, x₁} := by rw [hcross]; exact pair_comm _ _
  let T : TwoExit M := ⟨Y, hYM, x₂, x₁, hcross', hx, fun h => hne h.symm, ho2, ho1⟩
  have hpostdef : T.post = Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂)) := rfl
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hY1 : 1 ≤ Y.card := card_pos.mpr ⟨M.atom x₂, T.atom_x⟩
  have hopen' : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S := fun S hS _ => by
    rw [hpostdef] at hS ⊢; exact hopen S hS
  have hcB : T.c ∉ Bs := hv
  have hdB : T.d ∉ Bs := hu
  have hcount := T.countEFree_le_chain hcap hloop hdeg hch hYconn Bs hcB hdB hopen' hL hL11 hδ0 P Adm hAdm
  -- ranks
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨M.atom x₁, M.atom_mem x₁⟩ hMconn
  have hFp : (piece M Y).numComponents = 1 := Mole.numComponents_eq_one (piece M Y)
    (by rw [piece_atoms hYM]; exact ⟨M.atom x₂, T.atom_x⟩) (by rw [piece_atoms hYM]; exact hYconn)
  have hFq : T.post.numComponents = 1 :=
    Mole.numComponents_eq_one T.post ⟨T.c, by rw [T.post_atoms]; exact T.c_mem⟩ (by rw [hpostdef]; exact hpost)
  have hrkp : (piece M Y).circuitRank = 0 := by
    unfold Molecule.circuitRank
    rw [chain_piece_card M hYM hch hY1 hcross (fun h => hne (by rw [h])), piece_atoms hYM, hFp]
    push_cast; ring
  have hrk : M.circuitRank = T.post.circuitRank := by
    have := T.circuitRank_identity
    rw [hrkp, hF1, hFq, hFp] at this
    push_cast at this; linarith
  -- cells
  have hcellsP : MoleProp.ladderCells (piece M Y) = ∅ := by
    rw [T.ladderCells_piece_eq]
    refine eq_empty_of_forall_notMem fun S hS => ?_
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    refine no_cell_of_deg_le_two M (mem_filter.mp hS1).2 fun a ha => ?_
    have := Mole.outdeg_add_indeg M a; have := hch a (hS2 ha); omega
  have hcpP : ∀ P'' : Finset V → ℝ, MoleProp.cellProduct (piece M Y) L γ δ P'' = 1 := fun P'' => by
    unfold MoleProp.cellProduct; rw [hcellsP]; simp
  have hbpos : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < C1 := by linarith
    positivity
  have hnorm : ∀ P' ∈ T.scaleFamily L P, MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization T.post (d := d) L γ δ C1 P' * (Real.log L ^ 2) ^ 6 := by
    intro P' hP'
    have hP'nn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
      have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
      exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M hcell.1), hcell.1⟩))
    have hagree := T.scaleFamily_agree hP'
    have hcells := T.cellProduct_le (γ := γ) hloop hdeg hLp.le hδ0.le hlog P P' hP hP'nn hagree
    have hcp : MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6 := by
      have h := hcells
      change MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct (piece M T.Y) L γ δ P *
        MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6 at h
      rwa [hcpP, one_mul] at h
    unfold MoleProp.freeNormalization
    rw [hrk]
    have hX : 0 ≤ L ^ (-((d : ℝ) - γ) * (T.post.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ T.post.circuitRank := by
      positivity
    calc _ ≤ L ^ (-((d : ℝ) - γ) * (T.post.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ T.post.circuitRank *
          (MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6) := mul_le_mul_of_nonneg_left hcp hX
      _ = _ := by ring
  -- the constant
  have hconst : ((5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ) : ℝ) * (Real.log L ^ 2) ^ 6 ≤
      21125 * Real.log L ^ (14 : ℝ) := by
    have hS5 := card_scaleSet_le_log hlog
    have hfam : ((T.scaleFamily L P).card : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := by
      exact_mod_cast T.card_scaleFamily_le hloop hdeg L P
    have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
    have hl0 : 0 ≤ Real.log L := by linarith
    have hK : (T.windowK : ℝ) ≤ 13 := by
      have : T.windowK ≤ 13 := by unfold TwoExit.windowK; change 1 + 4 * Y.card ≤ 13; omega
      exact_mod_cast this
    have h14 : Real.log L ^ (14 : ℝ) = Real.log L ^ 14 := by
      rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h14]
    push_cast
    have h1 : ((scaleSet L).card : ℝ) ^ 2 ≤ (5 * Real.log L) ^ 2 := pow_le_pow_left₀ hS0 hS5 2
    have h2 : (T.windowK : ℝ) ^ 2 ≤ 13 ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hK 2
    calc 5 * (T.windowK : ℝ) ^ 2 * ((T.scaleFamily L P).card : ℝ) * (Real.log L ^ 2) ^ 6
        ≤ 5 * 13 ^ 2 * (5 * Real.log L) ^ 2 * (Real.log L ^ 2) ^ 6 := by
          gcongr
          exact hfam.trans h1
      _ = 21125 * Real.log L ^ 14 := by ring
  -- assemble
  set fam := T.scaleFamily L P with hfam
  set G := ⨆ P' ∈ fam, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P') with hG
  rw [MoleProp.countAFree_eq_normalization]
  have hstep : (G : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P) ≤
      ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
        AFreeSupAdm T.post d L γ δ C1 (fun P' κ' => lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P' κ') := by
    rw [hG]
    simp only [ENat.toENNReal_iSup, ENNReal.iSup_mul]
    refine iSup₂_le fun P' hP' => ?_
    have hP'nn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
      have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
      exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M hcell.1), hcell.1⟩))
    have hnq := MoleProp.freeNormalization_pos T.post (d := d) (γ := γ) hLp hδ0 (by linarith : (0 : ℝ) < C1) hlog0 P'
      hP'nn
    calc (MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P') : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
        ≤ (MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P') : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization T.post (d := d) L γ δ C1 P' * (Real.log L ^ 2) ^ 6) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hnorm P' hP'))
      _ = ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
          MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P') P' := by
          rw [MoleProp.countAFree_eq_normalization, ENNReal.ofReal_mul hnq.le]; ring
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          exact le_iSup₂_of_le (f := fun P'' (_ : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P'' S) =>
            MoleProp.countAFree T.post L γ δ C1 (0 : Mom d)
              (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P'') P'') P' hP'nn le_rfl
  have hcount' : (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤
      ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (G : ℝ≥0∞) := by
    have h := ENat.toENNReal_mono hcount
    have e : (((5 * (T.windowK : ℕ∞) ^ 2 * (fam.card : ℕ∞) : ℕ∞)) : ℝ≥0∞) =
        ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) := by
      have : (5 * (T.windowK : ℕ∞) ^ 2 * (fam.card : ℕ∞) : ℕ∞) = ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℕ∞) := by
        push_cast; rfl
      rw [this, ENat.toENNReal_coe]
    rw [ENat.toENNReal_mul, e] at h
    exact h
  calc (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
      ≤ ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (G : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P) := mul_le_mul' hcount' le_rfl
    _ = ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * ((G : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)) := by ring
    _ ≤ ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
        AFreeSupAdm T.post d L γ δ C1 (fun P' κ' => lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P' κ')) :=
        mul_le_mul' le_rfl hstep
    _ = ENNReal.ofReal (((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ) * (Real.log L ^ 2) ^ 6) *
        AFreeSupAdm T.post d L γ δ C1 (fun P' κ' => lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P' κ') := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; ring
    _ ≤ ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        AFreeSupAdm T.post d L γ δ C1 (fun P' κ' => lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P' κ') :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl

/-- **`OpDInput`** (DH23 L1865–L1867), with the hypotheses of `OpDAt`; any `γ`, `η > 0`. -/
theorem opDInput (d : ℕ) (γ η : ℝ) (hη : 0 < η) : OpDInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨21125, 14, max (Real.exp 1) ((11 : ℝ) ^ (2 / η)), fun L hL => ?_⟩⟩
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans hL
  have hL11' : (11 : ℝ) ^ (2 / η) ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11 : 11 ≤ L ^ (η / 2) := by
    calc (11 : ℝ) = ((11 : ℝ) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ L ^ (η / 2) := Real.rpow_le_rpow (by positivity) hL11' (by positivity)
  exact @opDAt.{u, v} d L γ δ η C1 hη hL1 hlog hL11 hδ hC1

end WaveTurbulence.FinalCountG8
